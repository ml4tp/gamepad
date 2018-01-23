from time import time

import torch
import torch.autograd as autograd
import torch.nn as nn
import torch.nn.functional as F
import torch.optim as optim
from tqdm import tqdm
import numpy as np
import os

# -------------------------------------------------
# Helper
from ml.poseval.fold_model import TacStFolder, Folder
from ml.utils import ResultLogger, cpuStats, Timer, currTS

# -------------------------------------------------
# Training
def iter_data(data, size, shuffle = False):
    n = len(data)
    n_end = (n // size)*size
    if shuffle:
        perm = np.random.permutation(n)[:n_end]
        data = [data[i] for i in perm]
    for start in range(0, n_end, size):
        yield data[start : start + size]

class PosEvalTrainer(object):
    def __init__(self, model, tactrs, poseval_dataset, args):
        # Other state
        self.args = args
        self.tactrs = tactrs
        self.poseval_dataset = poseval_dataset

        # Model
        self.model = model       # PyTorch model
        self.torch = torch
        if args.cuda:
            self.model.cuda()
            self.torch = torch.cuda

        # Optimizer
        self.loss_fn =  nn.CrossEntropyLoss()
        self.opt = optim.Adam(self.model.parameters(), lr=args.lr)

        # Training
        self.max_epochs = 10000
        self.epochs = 0
        self.updates = 0
        self.best_accuracy = 0.0
        self.best_loss = np.inf

        # Folder
        self.folder = Folder(model, args.fold, args.cuda)
        self.tacst_folder = {}   # Folder to embed
        for tactr_id, tactr in enumerate(self.tactrs):
            self.tacst_folder[tactr_id] = TacStFolder(model, tactr, self.folder)

        misc = "_".join([v for k,v in (zip([args.lstm, args.treelstm], ["lstm", "treelstm"])) if k])
        basepath = 'mllogs/sgv_nb_{}_lr_{}_ln_{}_m_{}_r_{}/'.format(args.nbatch, args.lr, args.ln, misc, args.name)
        if args.mload:
            self.load(args.mload)
            basepath += 'load_{}/'.format(self.ts)  # So reloaded models saved in subdirectory

        if not os.path.exists(basepath):
            os.makedirs(basepath)

        self.savepath = basepath + '{}.pth'
        self.logpath = basepath + 'log.jsonl'
        self.vallogpath = basepath + 'log_val.jsonl'

        print("Logging to ", self.logpath, "and Saving models to ", self.savepath)
        self.logger = ResultLogger(self.logpath)
        self.vallogger = ResultLogger(self.vallogpath)


    def save(self, accuracy = 0.0, loss = np.inf):
        self.ts = currTS()
        savepath = self.savepath.format(self.ts)
        print("Saving at", savepath)
        checkpoint = {
            'model': self.model.state_dict(),
            'opt': self.opt.state_dict(),
            'args': self.args,
            'epochs': self.epochs,
            'updates': self.updates,
            'accuracy': accuracy,
            'loss': loss,
            'ts': self.ts,
        }
        torch.save(checkpoint, savepath)
        print("Done saving")

    def load(self, path):
        print("Loading from ", path)
        checkpoint = torch.load(path)
        self.model.load_state_dict(checkpoint['model'])
        self.opt.load_state_dict(checkpoint['opt'])
        #self.args = checkpoint.args  # Use currently passed arguments
        self.epochs = checkpoint['epochs']
        self.updates = checkpoint['updates']
        self.best_accuracy = checkpoint['accuracy']
        self.best_loss = checkpoint['loss']
        self.ts = checkpoint['ts']
        print("Done loading")

    def forward(self, minibatch):
        n_batch = len(minibatch)
        self.folder.reset()  # Before or after?
        all_logits, all_targets = [], []
        astsizes = 0
        # Forward and Backward graph
        for tactr_id, poseval_pt in minibatch:
            self.tacst_folder[tactr_id].reset()

        for tactr_id, poseval_pt in minibatch:
            tacst_folder = self.tacst_folder[tactr_id]
            astsizes += poseval_pt.tacst_size
            # Apply forward pass

            all_logits += [tacst_folder.fold_tacst(poseval_pt.tacst)]
            all_targets += [poseval_pt.subtr_bin]

        # print(self.folder)
        res = self.folder.apply(all_logits)
        logits = res[0]
        targets = autograd.Variable(self.torch.LongTensor(all_targets), requires_grad=False)
        assert logits.shape == torch.Size([n_batch, 3])  # , folded_logits[0].shape
        loss = self.loss_fn(logits, targets)
        preds = torch.max(logits, dim=-1)[1]  # 0-th is max values, 1-st is max location
        correct = torch.sum(torch.eq(preds, targets).cpu())
        accuracy = float(correct.data) / float(np.prod(preds.shape))
        return loss, accuracy, astsizes

    def train(self):
        # if args.mload:
        #     self.load(args.mload)

        # Data info
        for k in ['train', 'val', 'test']:
            data = getattr(self.poseval_dataset, k)
            ys = [poseval_pt.subtr_bin for _, poseval_pt in data]
            print("{} Len={} SubtrSizeBins={}".format(k, len(data), dict(zip(*np.unique(ys, return_counts=True)))))

        # Training info
        data = self.poseval_dataset.train
        n_batch = self.args.nbatch
        n_train = len(data)

        # Model Info
        total_params = 0
        for param in self.model.parameters():
            total_params += np.prod(param.shape)
            print(param.shape)
        print("Total Parameters ", total_params)

        # State info
        for k,v in self.model.state_dict().items():
            print(k, v.shape)
        for k,v in self.opt.state_dict().items():
            print(k)

        # Train
        smooth_acc = None
        smooth_loss = None
        while self.epochs < self.max_epochs:
            testart = time()
            for minibatch in tqdm(iter_data(data, shuffle = True, size = n_batch), total = n_train // n_batch, ncols = 80, leave = False):
                with Timer() as t:
                    # Prepare to compute gradients
                    self.model.zero_grad()

                    # Forward pass
                    loss, accuracy, astsizes = self.forward(minibatch)

                    # Metrics
                    if not smooth_acc:
                        smooth_acc = accuracy
                        smooth_loss = loss.data
                    else:
                        smooth_acc = 0.01 * accuracy + 0.99 * smooth_acc
                        smooth_loss = 0.01 * loss.data + 0.99 * smooth_loss

                    # Backward pass
                    loss.backward()
                    self.opt.step()

                self.updates += 1
                tqdm.write("Update %d Loss %.4f Accuracy %0.4f SmAccuracy %.4f Interval %.4f AstSizes %d TpN %0.4f TpE %0.4f" % (self.updates, loss.data, accuracy, smooth_acc, t.interval, astsizes, t.interval*1e3 / astsizes, t.interval / n_batch))
                self.logger.log(epoch=self.epochs, updates=self.updates, loss="%0.4f" % loss.data, acc="%0.4f" % accuracy, smooth_loss = "%0.4f" % smooth_loss, smooth_acc = "%0.4f" % smooth_acc)
                    # if idx % 10 == 0:
                    #     cpuStats()
                        # memReport()
                    # if idx == 6:
                    #     print("Epoch Time with sh2 %.4f Loss %.4f" % (time() - testart, total_loss))
                    #     assert False
                if self.args.debug:
                    if self.updates % 10 == 0:
                        exit()
                if self.updates % 1000 == 100:
                    self.validate()
            self.epochs += 1
            tqdm.write("Finished Epoch %0.4f Time %.4f" % (self.epochs, time() - testart))

    def validate(self):
        print("Validating")
        epochs = self.epochs
        updates = self.updates
        data = self.poseval_dataset.val
        n_batch = self.args.valbatch
        n_train = len(data)
        losses = []
        accuracies = []
        for minibatch in tqdm(iter_data(data, shuffle = False, size = n_batch), total = n_train // n_batch, ncols = 80, leave = False):
            with Timer() as t:
                loss, accuracy, astsizes = self.forward(minibatch)
            losses.append(loss.data)
            accuracies.append(accuracy)
            tqdm.write("Update %d Loss %.4f Accuracy %0.4f Interval %.4f TpE %0.4f" %
                           (updates, loss.data, accuracy, t.interval, t.interval / len(minibatch)))
        loss = float(np.mean(losses))
        accuracy = float(np.mean(accuracies))
        self.best_loss = min(self.best_loss, loss)
        self.best_accuracy = max(self.best_accuracy, accuracy)
        tqdm.write("Epoch %d Updates %d Loss %0.4f Accuracy %0.4f" % (self.epochs, self.updates, loss, accuracy))
        self.vallogger.log(epoch=epochs, updates=updates, loss="%0.4f" % loss, acc = "%0.4f" % accuracy, best_loss = "%0.4f" % self.best_loss, best_acc = "%0.4f" % self.best_accuracy)
        self.save(accuracy, loss)

#     def finalize(self):
#         # Save the model (parameters only)
#         timestamp = currTS()
#         dirname = "mllogs/"
#         filename = "./" + dirname + "model-{}.params".format(timestamp)
#         print("Saving model to {}...".format(filename))
#         torch.save(self.model.state_dict(), filename)
#         self.logger.close()
#         return filename
#
# class PosEvalInfer(object):
#     def __init__(self, tactrs, model, f_fold=True):
#         self.tactrs = tactrs
#         self.model = model
#
#         self.tacst_folder = {}   # Folder to embed
#         for tactr_id, tactr in enumerate(self.tactrs):
#             self.tacst_folder[tactr_id] = TacStFolder(model, tactr, f_fold)
#
#     def infer(self, poseval_test):
#         preds = []
#         for idx, (tactr_id, poseval_pt) in enumerate(poseval_test):
#             torun_logits, torun_labels = [], []
#             folder = self.tacst_folder[tactr_id]
#             folder.reset()
#             torun_logits += [folder.fold_tacst(poseval_pt.tacst)]
#             torun_labels += [0]
#             res = folder.apply(torun_logits, torun_labels)
#             logits = res[0].data.numpy()
#             preds += [np.argmax(logits)]
#             print("Logits", logits, "Predicted", np.argmax(logits), "Actual", poseval_pt.subtr_bin)
#         return preds


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
