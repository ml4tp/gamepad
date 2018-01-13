from time import time

import torch
import torch.autograd as autograd
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim

import numpy as np
from ml.poseval.fold_model import TacStFolder, Folder
from ml.utils import ResultLogger, cpuStats, Timer

# -------------------------------------------------
# Helper


# -------------------------------------------------
# Training

np.random.seed(0)
torch.manual_seed(0)
logger = ResultLogger('mllogs/embedv1.0.jsonl')

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

    def train(self, epochs=20, lemmabatch = 64):
        losses = []
        loss_fn = nn.CrossEntropyLoss()
        opt = optim.Adam(self.model.parameters(), lr=0.001)
        lemmas = len(self.poseval_dataset)
        for epoch in range(epochs):
            testart = time()
            total_loss = torch.Tensor([0])
            perm = np.random.permutation(lemmas)
            index = lemmabatch
            currbatch = perm[:index]
            for idx, (tactr_id, poseval_pt) in enumerate(self.poseval_dataset):
                print("Training ({}/{}) TacSt={}, AstSize={}".format(tactr_id, len(self.tactrs), idx, poseval_pt.tacst_size))
                with Timer() as t:                    
                    # Prepare to compute gradients
                    self.model.zero_grad()
                    folder = self.tacst_folder[tactr_id]
                    folder.reset()  # Uncomment to enable sh2. TODO(deh): reset this when?

                    # Apply forward pass
                    all_logits, all_targets = [], []
                    all_logits += [folder.fold_tacst(poseval_pt.tacst)]
                    all_targets += [poseval_pt.subtr_bin]
                    #print(folder.folder)
                    res = folder.apply(all_logits, all_targets)

                    # Backprop
                    loss = loss_fn(res[0], res[1])
                    loss.backward(retain_graph=True)
                    opt.step()
                    total_loss += loss.data
                print("Loss %.4f %.4f" % (loss.data, t.interval))
                logger.log(n_epochs=epoch, niters=idx, loss="%0.4f" % loss.data)
                # if idx % 10 == 0:
                #     cpuStats()
                    # memReport()
                if idx == 6:
                    print("Epoch Time with sh2 %.4f Loss %.4f" % (time() - testart, total_loss))
                    assert False
            print("Epoch Time %.4f Loss %.4f" % (time() - testart, total_loss))
            losses.append(total_loss)
        logger.close()
        print("Losses", losses)
