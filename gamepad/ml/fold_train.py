import os
from time import time

import numpy as np
import torch
import torch.autograd as autograd
import torch.nn as nn
import torch.optim as optim
from tqdm import tqdm

from ml.fold_model import TacStFolder, Folder
from ml.utils import ResultLogger, Timer, curr_timestamp, torch_summarize_df


# -------------------------------------------------
# Training

def iter_data(data, size, shuffle=False):
    n = len(data)
    n_end = (n // size)*size
    if shuffle:
        perm = np.random.permutation(n)[:n_end]
        data = [data[i] for i in perm]
    for start in range(0, n_end, size):
        yield data[start: start + size]


class TacStTrainer(object):
    def __init__(self, model, tactrs, tacst_dataset, args):
        # Other state
        self.args = args
        self.tactrs = tactrs
        self.tacst_dataset = tacst_dataset

        # Model
        self.model = model       # PyTorch model
        self.torch = torch
        if args.cuda:
            self.model.cuda()
            self.torch = torch.cuda

        # Optimizer
        self.loss_fn = nn.CrossEntropyLoss()
        self.opt = optim.Adam(self.model.parameters(), lr=args.lr)

        # Training
        self.max_epochs = 10000
        self.epochs = 0
        self.updates = 0
        self.best_accuracy = 0.0
        self.best_loss = np.inf
        self.ts = None               # timestamp

        typ = "_".join([v for k, v in (zip([not (args.midlvl or args.noimp), args.midlvl, args.noimp],
                                           ["kern", "midlvl", "noimp"])) if k])
        if self.model.f_linear:
            # Linear
            basepath = 'mllogs/{}/type_{}_lr_{}_m_linear_r_{}'.format(args.task, typ, args.lr, args.name)
        else:
            # Folder
            self.folder = Folder(model, args.fold, args.cuda)
            self.tacst_folder = {}   # Folder to embed
            for tactr_id, tactr in enumerate(self.tactrs):
                self.tacst_folder[tactr_id] = TacStFolder(model, tactr, self.folder)

            misc = "_".join([v for k, v in (zip([not (args.lstm or args.treelstm), args.lstm, args.treelstm],
                                                ["gru", "lstm", "treelstm"])) if k])

            basepath = 'mllogs/{}/type_{}_state_{}_lr_{}_conclu_pos_{}_ln_{}_drop_{}_wd_{}_v_{}_attn_{}_heads_{}_m_{}_r_{}/'.format(args.task, typ, args.state, args.lr, args.conclu_pos, args.ln, args.dropout, args.weight_dropout, args.variational, args.attention, args.heads, misc, args.name)

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

    def save(self, accuracy=0.0, loss=np.inf):
        self.ts = curr_timestamp()
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
        # self.args = checkpoint.args  # Use currently passed arguments
        self.epochs = checkpoint['epochs']
        self.updates = checkpoint['updates']
        self.best_accuracy = checkpoint['accuracy']
        self.best_loss = checkpoint['loss']
        self.ts = checkpoint['ts']
        print("Done loading")

    def forward(self, minibatch):
        n_batch = len(minibatch)
        if self.model.f_linear:
            # Simple linear model
            features = []
            astsizes = 0
            for tactr_id, tacst_pt in minibatch:
                features.append(self.model.get_features(tacst_pt))
                astsizes += tacst_pt.kern_size
            features = autograd.Variable(self.torch.FloatTensor(features))
            logits = self.model.pred(features)
        else:
            # Folding model
            self.folder.reset()  # Before or after?
            logits, targets = [], []
            astsizes = 0
            # Forward and Backward graph
            for tactr_id, tacst_pt in minibatch:
                self.tacst_folder[tactr_id].reset()
            for tactr_id, tacst_pt in minibatch:
                tacst_folder = self.tacst_folder[tactr_id]
                # TODO (praf): Use different size depending on flag
                astsizes += tacst_pt.kern_size
                # Apply forward pass

                pred = tacst_folder.fold_tacst(tacst_pt)
                logits += [pred]
                if self.args.task == 'pose':
                    targets += [tacst_pt.subtr_bin]
                else:
                    targets += [tacst_pt.tac_bin]
            logits = self.folder.apply(logits)[0]  # Folded model

        targets = autograd.Variable(self.torch.LongTensor(targets), requires_grad=False)
        assert logits.shape == torch.Size([n_batch, self.model.outsize])  # , folded_logits[0].shape
        loss = self.loss_fn(logits, targets)
        preds = torch.max(logits, dim=-1)[1]  # 0-th is max values, 1-st is max location
        correct = torch.sum(torch.eq(preds, targets).cpu())
        accuracy = float(correct.data) / float(np.prod(preds.shape))

        return logits, loss, accuracy, astsizes

    def train(self):
        # if args.mload:
        #     self.load(args.mload)

        # Data info
        for k in ['train', 'val', 'test']:
            data = getattr(self.tacst_dataset, k)
            if self.args.task == 'pose':
                ys = [tacst_pt.subtr_bin for _, tacst_pt in data]
            else:
                ys = [tacst_pt.tac_bin for _, tacst_pt in data]

            print("{} Len={} SubtrSizeBins={}".format(k, len(data), dict(zip(*np.unique(ys, return_counts=True)))))

        # Training info
        data = self.tacst_dataset.train
        n_batch = self.args.nbatch
        n_train = len(data)

        # Model info
        print(torch_summarize_df(self.model))

        # Parameters
        total_params = 0
        learnable_params = 0
        param_names = set()
        for name, param in self.model.named_parameters():
            param_names.add(name)
            total_params += np.prod(param.shape)
            if param.requires_grad:
                learnable_params += np.prod(param.shape)
            print(name, param.shape, param.requires_grad)

        print("Total Parameters", total_params)
        print("Learnable Parameters", learnable_params)

        grad_params = [(name, p) for name, p in self.model.named_parameters() if p.requires_grad]

        # Other model state
        for k, v in self.model.state_dict().items():
            if k not in param_names:
                print(k, v.shape, "False", "state")

        # Optimizer State info
        for k, v in self.opt.state_dict().items():
            print(k, v)

        # Train
        smooth_acc = None
        smooth_loss = None
        while self.epochs < self.max_epochs:
            testart = time()
            for minibatch in tqdm(iter_data(data, shuffle=True, size=n_batch),
                                  total=n_train // n_batch, ncols=80, leave=False):
                with Timer() as t:
                    # Set model to traiing mode (needed for dropout, batchnorm etc)
                    self.model.train()
                    # Prepare to compute gradients
                    self.model.zero_grad()

                    # Forward pass
                    _, loss, accuracy, astsizes = self.forward(minibatch)

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

                    # Gradient metrics
                    grads = {}
                    sgrads = {}
                    for (name, p) in grad_params:
                        if p.grad is not None:
                            gg = float(torch.norm(p.grad).data)
                            grads[name] = "%0.8f" % gg
                            sgrads[name] = "%0.4f" % gg
                        else:
                            grads[name] = "0.0"
                            sgrads[name] = "0.0"

                self.updates += 1
                tqdm.write("Update %d Loss %.4f Accuracy %0.4f SmAccuracy %.4f Interval %.4f AstSizes %d TpN %0.4f TpE %0.4f" % (self.updates, loss.data, accuracy, smooth_acc, t.interval, astsizes, t.interval*1e3 / astsizes, t.interval / n_batch))
                self.logger.log(epoch=self.epochs, updates=self.updates, loss="%0.4f" % loss.data,
                                acc="%0.4f" % accuracy, smooth_loss="%0.4f" % smooth_loss,
                                smooth_acc="%0.4f" % smooth_acc, **grads)
                if self.updates % 10 == 0 or self.args.debug:
                    tqdm.write("Grad norms")
                    for gg in sgrads.items():
                        tqdm.write("%s %s" % gg)
                if self.args.debug:
                    if self.updates % 10 == 0:
                        return
                if self.updates % 1000 == 100:
                    self.validate()
            self.epochs += 1
            tqdm.write("Finished Epoch %0.4f Time %.4f" % (self.epochs, time() - testart))

    def validate(self):
        # Set model to evaluation mode (needed for dropout)
        self.model.eval()
        print("Validating")
        epochs = self.epochs
        updates = self.updates
        data = self.tacst_dataset.val
        n_batch = self.args.valbatch
        n_train = len(data)
        losses = []
        accuracies = []
        for minibatch in tqdm(iter_data(data, shuffle=False, size=n_batch),
                              total=n_train // n_batch, ncols=80, leave=False):
            with Timer() as t:
                _, loss, accuracy, astsizes = self.forward(minibatch)
            losses.append(loss.data)
            accuracies.append(accuracy)
            tqdm.write("Update %d Loss %.4f Accuracy %0.4f Interval %.4f TpE %0.4f" %
                       (updates, loss.data, accuracy, t.interval, t.interval / len(minibatch)))
        loss = float(np.mean(losses))
        accuracy = float(np.mean(accuracies))
        self.best_loss = min(self.best_loss, loss)
        self.best_accuracy = max(self.best_accuracy, accuracy)
        tqdm.write("Epoch %d Updates %d Loss %0.4f Accuracy %0.4f" % (self.epochs, self.updates, loss, accuracy))
        self.vallogger.log(epoch=epochs, updates=updates, loss="%0.4f" % loss, acc="%0.4f" % accuracy,
                           best_loss="%0.4f" % self.best_loss, best_acc="%0.4f" % self.best_accuracy)
        self.save(accuracy, loss)
