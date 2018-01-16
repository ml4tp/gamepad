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

def iter_data(data, size, shuffle = False):
    n = len(data)
    n_end = (n // size)*size
    if shuffle:
        perm = np.random.permutation(n)[:n_end]
        data = [data[i] for i in perm]
    for start in range(0, n_end, size):
        yield data[start : start + size]

def save(model, path):
    print("Saving model at ", path)
    state_dict = model.state_dict()
    for k,v in state_dict.items():
        print(k, v.size())
    torch.save(state_dict, path)
    print("Done saving")

def load(model, path):
    print("Loading model at ", path)
    model.load_state_dict(torch.load(path))
    print("Done loading")

class PosEvalTrainer(object):
    def __init__(self, model, tactrs, poseval_dataset, foldy, cuda):
        # Other state
        self.tactrs = tactrs
        self.poseval_dataset = poseval_dataset  

        # Model
        self.model = model       # PyTorch model
        self.torch = torch
        if cuda:
            self.model.cuda()
            self.torch = torch.cuda
        self.folder = Folder(model, foldy, cuda)
        self.tacst_folder = {}   # Folder to embed
        for tactr_id, tactr in enumerate(self.tactrs):
            self.tacst_folder[tactr_id] = TacStFolder(model, tactr, self.folder)

    def train(self, args):
        if args.mload:
            load(self.model, args.mload)
        logloc = 'mllogs/gv_nb_{}_lr_{}_ln_{}_r_{}.jsonl'.format(args.nbatch, args.lr, args.ln, args.name)
        saveloc = logloc[:-5] + 'pth'
        print("Logging to ", logloc, "and Saving model to ", saveloc)
        logger = ResultLogger(logloc)
        n_epochs = 10000
        n_batch = args.nbatch
        losses = []
        total_params = 0
        for param in self.model.parameters():
            total_params += np.prod(param.shape)
            print(param.shape)
        print("Total Parameters ", total_params)
        opt = optim.Adam(self.model.parameters(), lr=args.lr)
        n_train = len(self.poseval_dataset)
        loss_fn = nn.CrossEntropyLoss()
        updates = 0
        ys = [poseval_pt.subtr_bin for _, poseval_pt in self.poseval_dataset]
        print("Counts ", dict(zip(*np.unique(ys, return_counts=True))))
        for epoch in range(n_epochs):
            if epoch % 10 == 0:
                save(self.model, saveloc)
            testart = time()
            total_loss = 0.0
            smooth_acc = None
            for minibatch in tqdm(iter_data(self.poseval_dataset, shuffle = True, size = n_batch), total = n_train // n_batch, ncols = 80, leave = False):
                with Timer() as t:
                    # Prepare to compute gradients
                    self.model.zero_grad()
                    self.folder.reset() # Before or after?
                    all_logits, all_targets = [], []
                    astsizes = 0
                    # Forward and Backward graph
                    for tactr_id, poseval_pt in minibatch:
                        self.tacst_folder[tactr_id].reset()

                    for tactr_id, poseval_pt in minibatch:
                        tacst_folder = self.tacst_folder[tactr_id]
                        #print("Training ({}/{}) AstSize={}".format(tactr_id, len(self.tactrs), poseval_pt.tacst_size))
                        astsizes += poseval_pt.tacst_size
                        # Apply forward pass

                        all_logits += [tacst_folder.fold_tacst(poseval_pt.tacst)]
                        all_targets += [poseval_pt.subtr_bin]

                    #print(self.folder)
                    res = self.folder.apply(all_logits)
                    logits = res[0]
                    targets = autograd.Variable(self.torch.LongTensor(all_targets), requires_grad=False)
                    assert logits.shape == torch.Size([n_batch, 3]) #, folded_logits[0].shape
                    # Backprop
                    loss = loss_fn(logits, targets)
                    preds = torch.max(logits, dim = -1)[1] # 0-th is max values, 1-st is max location
                    correct = torch.sum(torch.eq(preds, targets).cpu())
                    accuracy = float(correct.data) / float(np.prod(preds.shape))
                    if not smooth_acc:
                        smooth_acc = accuracy
                    else:
                        smooth_acc = 0.01 * accuracy + 0.99 * smooth_acc
                    loss.backward()
                    opt.step()
                updates += 1
                total_loss += loss.data
                tqdm.write("Update %d Loss %.4f Accuracy %0.4f SmAccuracy %.4f Interval %.4f AstSizes %d TpN %0.4f TpE %0.4f" % (updates, loss.data, accuracy, smooth_acc, t.interval, astsizes, t.interval / astsizes, t.interval / n_batch))
                logger.log(epoch=epoch, updates=updates, loss="%0.4f" % loss.data, acc="%0.4f" % accuracy, smooth_acc = "%0.4f" % smooth_acc)
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
