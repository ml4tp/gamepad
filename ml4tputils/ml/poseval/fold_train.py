from time import time

import torch
import torch.autograd as autograd
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
from tqdm import tqdm
import numpy as np
from ml.poseval.fold_model import TacStFolder, Folder
from ml.utils import ResultLogger, cpuStats, Timer

# -------------------------------------------------
# Helper


# -------------------------------------------------
# Training

np.random.seed(0)
torch.manual_seed(0)
logger = ResultLogger('mllogs/mbfoldembedv1.0.jsonl')

def iter_data(data, size, shuffle = False):
    n = len(data)
    n_end = (n // size)*size
    if shuffle:
        perm = np.random.permutation(n)[:n_end]
        data = [data[i] for i in perm]
    for start in range(0, n_end, size):
        yield data[start : start + size]

class PosEvalTrainer(object):
    def __init__(self, model, tactrs, poseval_dataset, foldy):
        # Other state
        self.tactrs = tactrs
        self.poseval_dataset = poseval_dataset  

        # Model
        self.model = model       # PyTorch model
        self.folder = Folder(model, foldy)
        self.tacst_folder = {}   # Folder to embed
        for tactr_id, tactr in enumerate(self.tactrs):
            self.tacst_folder[tactr_id] = TacStFolder(model, tactr, self.folder)

    def train(self, n_epochs=20, n_batch=32):
        losses = []
        opt = optim.Adam(self.model.parameters(), lr=0.001)
        n_train = len(self.poseval_dataset)
        loss_fn = nn.CrossEntropyLoss()
        updates = 0
        for epoch in range(n_epochs):
            testart = time()
            total_loss = torch.Tensor([0])
            for minibatch in iter_data(self.poseval_dataset, shuffle = True, size = n_batch):#, total = n_train // n_batch, ncols = 80, leave = False):
                with Timer() as t:
                    # Prepare to compute gradients
                    self.model.zero_grad()
                    self.folder.reset() # Before or after?
                    logits, targets = [], []
                    astsizes = 0
                    # Forward and Backward graph
                    for tactr_id, poseval_pt in minibatch:
                        self.tacst_folder[tactr_id].reset()

                    for tactr_id, poseval_pt in minibatch:
                        tacst_folder = self.tacst_folder[tactr_id]
                        print("Training ({}/{}) AstSize={}".format(tactr_id, len(self.tactrs), poseval_pt.tacst_size))
                        astsizes += poseval_pt.tacst_size
                        # Apply forward pass

                        logits += [tacst_folder.fold_tacst(poseval_pt.tacst)]
                        targets += [poseval_pt.subtr_bin]

                    #print(self.folder)
                    folded_logits = self.folder.apply(logits)
                    assert folded_logits[0].shape == torch.Size([n_batch, 3]) #, folded_logits[0].shape
                    # Backprop
                    loss = loss_fn(folded_logits[0], autograd.Variable(torch.LongTensor(targets), requires_grad = False))
                    loss.backward()
                    opt.step()
                updates += 1
                total_loss += loss.data
                print("Update %d Loss %.4f Interval %.4f AstSizes %d TpN %0.4f TpE %0.4f" % (updates, loss.data, t.interval, astsizes, t.interval / astsizes, t.interval / n_batch))
                logger.log(epoch=epoch, updates=updates, loss="%0.4f" % loss.data)
                    # if idx % 10 == 0:
                    #     cpuStats()
                        # memReport()
                    # if idx == 6:
                    #     print("Epoch Time with sh2 %.4f Loss %.4f" % (time() - testart, total_loss))
                    #     assert False
            print("Epoch Time %.4f Loss %.4f" % (time() - testart, total_loss))
            losses.append(total_loss)
        logger.close()
        print("Losses", losses)
