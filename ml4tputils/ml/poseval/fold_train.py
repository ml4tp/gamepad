import numpy as np
from time import time

import torch
import torch.autograd as autograd
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim

from ml.poseval.fold_model import TacStFolder
from ml.utils import ResultLogger, cpuStats, Timer, currTS


# -------------------------------------------------
# Training

# torch.manual_seed(0)
# logger = ResultLogger('mllogs/embedv1.0.jsonl')

class PosEvalTrainer(object):
    def __init__(self, model, tactrs, poseval_dataset, log_file,
                 f_dbg=False, f_fold=True):
        # Other state
        self.tactrs = tactrs
        self.poseval_dataset = poseval_dataset
        self.logger = ResultLogger(log_file)
        
        # Flags
        self.f_dbg = f_dbg       # Running for debug purposes?
        self.f_fold = f_fold     # Fold for batching?

        # Model
        self.model = model       # PyTorch model
        self.tacst_folder = {}   # Folder to embed
        for tactr_id, tactr in enumerate(self.tactrs):
            self.tacst_folder[tactr_id] = TacStFolder(model, tactr, f_fold)

        # TODO(deh): Reset!
        torch.manual_seed(0)

    def finalize(self):
        # Save the model (parameters only)
        timestamp = currTS()
        filename = "./model-{}.params".format(timestamp)
        print("Saving model to {}...".format(filename))
        torch.save(self.model.state_dict(), filename)
        self.logger.close()
        return filename

    def train(self, epochs=20):
        losses = []
        loss_fn = nn.CrossEntropyLoss()
        opt = optim.Adam(self.model.parameters(), lr=0.001)
        for epoch in range(epochs):
            testart = time()
            total_loss = torch.Tensor([0])
            
            # Outer loop? Should be looping over all minibatches
            for idx, (tactr_id, poseval_pt) in enumerate(self.poseval_dataset):
                print("Training ({}/{}) TacSt={}, AstSize={}".format(tactr_id, len(self.tactrs), idx, poseval_pt.tacst_size))
                with Timer() as t:                    
                    # Prepare to compute gradients
                    self.model.zero_grad()
                    folder = self.tacst_folder[tactr_id]
                    folder.reset()  # TODO(deh): reset this when?

                    # Apply forward pass
                    all_logits, all_targets = [], []
                    all_logits += [folder.fold_tacst(poseval_pt.tacst)]
                    all_targets += [poseval_pt.subtr_bin]
                    # print(folder.folder)
                    res = folder.apply(all_logits, all_targets)

                    # Backprop
                    loss = loss_fn(res[0], res[1])
                    loss.backward(retain_graph=True)
                    opt.step()
                    total_loss += loss.data
                print("Loss %.4f %.4f" % (loss.data, t.interval))
                self.logger.log(n_epochs=epoch, niters=idx, loss="%0.4f" % loss.data)
                # if idx % 10 == 0:
                #     cpuStats()
                    # memReport()
                if self.f_dbg and tactr_id == 5:
                    print("Epoch Time with sh2 %.4f Loss %.4f" % (time() - testart, total_loss))
                    losses.append(total_loss)
                    print("Losses", losses)
                    return losses
            print("Epoch Time %.4f Loss %.4f" % (time() - testart, total_loss))
            losses.append(total_loss)
        print("Losses", losses)
        return losses


class PosEvalInfer(object):
    def __init__(self, tactrs, model, f_fold=True):
        self.tactrs = tactrs
        self.model = model

        self.tacst_folder = {}   # Folder to embed
        for tactr_id, tactr in enumerate(self.tactrs):
            self.tacst_folder[tactr_id] = TacStFolder(model, tactr, f_fold)

    def infer(self, poseval_test):
        torun_logits = []
        torun_labels = [0 for _ in poseval_test]
        for idx, (tactr_id, poseval_pt) in enumerate(poseval_test):
            folder = self.tacst_folder[tactr_id]
            folder.reset()
            torun_logits += [folder.fold_tacst(poseval_pt.tacst)]
            res = folder.apply(torun_logits, torun_labels)
            for idx, (tactr_id, poseval_pt) in enumerate(poseval_test):
                print("HERE", res[0])
                logits = res[0].data.numpy()
                # label = res[1][idx].data.numpy()
                # print("Logits", logits, "Predicted", np.argmax(logits), "Actual", poseval_pt.subtr_bin)


# -------------------------------------------------
# Debugging helper

class ChkPosEvalTrainer(object):
    def __init__(self, trainer1, trainer2):
        assert isinstance(trainer1, PosEvalTrainer)
        assert isinstance(trainer2, PosEvalTrainer)

        self.trainer1 = trainer1
        self.trainer1.f_dbg = True
        self.trainer2 = trainer2
        self.trainer2.f_dbg = True

    def check(self):
        losses1 = self.trainer1.train(epochs=1)
        losses2 = self.trainer2.train(epochs=1)
        print("Losses1: ", losses1)
        print("Losses2: ", losses2)
        diff = [l1 - l2 for l1, l2 in zip(losses1, losses2)]
        print("Diff: ", diff)
        # print(all(map(lambda x: x < 0.001, diff)))
