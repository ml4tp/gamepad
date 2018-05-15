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
from ml.utils import ResultLogger, cpu_stats, Timer, curr_timestamp, torch_summarize_df, flatten


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

def ema(emas, xs, alpha = 0.99):
    new_emas = []
    for ema, x in zip(emas, xs):
        if ema is None:
            new_ema = x
        else:
            new_ema = alpha*ema + (1.-alpha)*x
        new_emas.append(new_ema)
    return new_emas

def tostr(lst):
    return ["%.4f" % l for l in lst]

def get_mask(lids):
    lids = np.array(lids)
    yes_inds = np.where(lids != 0)[0]
    no_inds = np.where(lids == 0)[0]
    n = min(yes_inds.size, 5)
    nd = min(no_inds.size, 5 - n)
    #print("yes bound at ", n)
    #print("no bound at ", nd)
    yes_chose = np.array([], dtype=np.int)
    no_chose = np.array([], dtype=np.int)
    if n > 0:
        yes_chose = np.random.choice(yes_inds, n, replace=False)
    if nd > 0:
        no_chose = np.random.choice(no_inds, nd, replace=False)
    return np.concatenate([no_chose, yes_chose])

def apply_mask(logits, targets, mask):
    return [logits[m] for m in mask], [targets[m] for m in mask]

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
            print("Moved model to GPU")
        # Select whether we want mid-level or kernel-level AST
        if self.args.midlvl:
            self.get_tacst = lambda pt: pt.mid_tacst()
        else:
            self.get_tacst = lambda pt: pt.kern_tacst()

        # Optimizer
        self.loss_fn =  nn.CrossEntropyLoss()
        self.weigted_loss_fn = nn.CrossEntropyLoss(weight=self.torch.FloatTensor([0.1, 0.9]))
        self.opt = optim.Adam(self.model.parameters(), lr=args.lr)

        # Training
        self.max_epochs = 10000
        self.epochs = 0
        self.updates = 0
        self.best_accuracy = 0.0
        self.best_loss = np.inf
        if self.args.lids:
            self.best_lids_accuracy = 0.0

        self.ts = None               # timestamp

        # Folder
        self.folder = Folder(model, args.fold, args.cuda)
        self.tacst_folder = {}   # Folder to embed
        for tactr_id, tactr in enumerate(self.tactrs):
            self.tacst_folder[tactr_id] = TacStFolder(model, tactr, self.folder)

        misc = "_".join([v for k,v in (zip([not (args.lstm or args.treelstm), args.lstm, args.treelstm], ["gru", "lstm", "treelstm"])) if k])
        type = "_".join([v for k,v in (zip([not (args.midlvl or args.noimp), args.midlvl, args.noimp], ["kern", "midlvl", "noimp"])) if k])

        if args.lids:
            base_dir = args.task + "_lids"
        else:
            base_dir = args.task
        basepath = 'mllogs/{}/type_{}_state_{}_lr_{}_conclu_pos_{}_ln_{}_drop_{}_wd_{}_v_{}_attn_{}_heads_{}_m_{}_r_{}/'.format(base_dir, type, args.state, args.lr, args.conclu_pos, args.ln, args.dropout, args.weight_dropout, args.variational, args.attention, args.heads, misc, args.name)
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

    def final(self, logits, targets, batch, outsize, flid=False):
        # logits = self.folder.apply(logits)[0]  # Returns a list of results per arg, so 0-th entry is logits
        # print("\nTargets ", dict(zip(*np.unique(targets, return_counts=True))))
        targets = autograd.Variable(self.torch.LongTensor(targets), requires_grad=False)
        assert logits.shape == torch.Size([batch, outsize])  # , folded_logits[0].shape
        assert targets.shape == torch.Size([batch])
        if flid and self.args.weighted:
            loss = self.weigted_loss_fn(logits, targets)
        else:
            loss = self.loss_fn(logits, targets)
        preds = torch.max(logits, dim=-1)[1]  # 0-th is max values, 1-st is max location
        preds, targets = preds.data.cpu().numpy().astype(int), targets.data.cpu().numpy().astype(int)
        correct = np.sum(np.equal(preds, targets))
        # correct = torch.sum(torch.eq(preds, targets).long())
        # print("Preds ",  dict(zip(*np.unique(preds, return_counts=True))))
        # print("Correct ", float(correct), float(np.prod(preds.shape)))
        accuracy = float(correct) / float(np.prod(preds.shape))
        if flid:
            eps = 1e-5
            true_positive = np.sum(preds * targets)
            precision = true_positive / (np.sum(preds) + eps)
            recall = true_positive / (np.sum(targets) + eps)
            return loss, accuracy, precision, recall

        return loss, accuracy

    def forward(self, minibatch):
        n_batch = len(minibatch)
        self.folder.reset()  # Before or after?
        logits, targets = [], []
        if self.args.lids:
            n_lids = 0
            logits_lids, targets_lids = [], []
        astsizes = 0
        # Forward and Backward graph
        for tactr_id, tacst_pt in minibatch:
            self.tacst_folder[tactr_id].reset()

        for tactr_id, tacst_pt in minibatch:
            tacst_folder = self.tacst_folder[tactr_id]
            #TODO (praf): Use different size depending on flag
            if not self.args.midlvl:
                astsizes += tacst_pt.kern_size
            elif not self.args.noimp:
                astsizes += tacst_folder.mid_size
            else:
                astsizes += tacst_folder.mid_noimp_size

            # Apply forward pass
            pred = tacst_folder.fold_tacst(self.get_tacst(tacst_pt))
            if self.args.lids:
                pred, pred_lids = pred
                logits.append(pred)

                # Masked negative mining
                lids = tacst_pt.lids
                if self.args.mask:
                    mask = get_mask(lids)
                    pred_lids, lids = apply_mask(pred_lids, lids, mask)
                logits_lids.extend(pred_lids)
                targets_lids.extend(lids)
                n_lids += len(lids)
            else:
                logits.append(pred)

            if self.args.task == 'pose':
                targets += [tacst_pt.subtr_bin]
            else:
                targets += [tacst_pt.tac_bin]

        if self.args.lids:
            logits, logits_lids = self.folder.apply(logits, logits_lids)
            loss, accuracy = self.final(logits, targets, n_batch, self.args.outsize)
            loss_lids, accuracy_lids, precision, recall = self.final(logits_lids, targets_lids, n_lids, 2,
                                                                     flid=True)
            # print("Losses", loss.data, loss_lids.data)
            return loss + loss_lids, accuracy, accuracy_lids, precision, recall, astsizes
        else:
            logits = self.folder.apply(logits)[0]
            loss, accuracy = self.final(logits, targets, n_batch, self.args.outsize)
            return loss, accuracy, astsizes

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
        for name,param in self.model.named_parameters():
            param_names.add(name)
            total_params += np.prod(param.shape)
            if param.requires_grad:
                learnable_params += np.prod(param.shape)
            print(name, param.shape, param.requires_grad)

        print("Total Parameters", total_params)
        print("Learnable Parameters", learnable_params)

        grad_params = [(name,p) for name,p in self.model.named_parameters() if p.requires_grad]

        # Other model state
        for k,v in self.model.state_dict().items():
            if k not in param_names:
                print(k,v.shape, "False", "state")

        # Optimizer State info
        for k,v in self.opt.state_dict().items():
            print(k, v)

        # Train
        metrics_emas = [None, None]
        metrics_names = ["loss", "acc", "smooth_loss", "smooth_acc"]
        if self.args.lids:
            metrics_emas = [None, None, None]
            metrics_names = ["loss", "acc", "acc_lids", "precision", "recall", "smooth_loss", "smooth_acc",
                             "smooth_acc_lids", "smooth_precision", "smooth_recall"]

        while self.epochs < self.max_epochs:
            testart = time()
            for minibatch in tqdm(iter_data(data, shuffle=True, size=n_batch), total=n_train // n_batch, ncols=80, leave=False):
                with Timer() as t:
                    # Set model to traiing mode (needed for dropout, batchnorm etc)
                    self.model.train()
                    # Prepare to compute gradients
                    self.model.zero_grad()

                    # Forward pass
                    loss, *accuracies, astsizes = self.forward(minibatch)

                    # Metrics
                    metrics = [loss.data, *accuracies]
                    metrics_emas = ema(metrics_emas, metrics)

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
                metrics_zip = list(zip(metrics_names, tostr(metrics + metrics_emas)))
                metrics_log = " ".join(["%s %s" % (name, val) for (name, val) in metrics_zip])
                tqdm.write("Update %d %s Interval %.4f AstSizes %d TpN %0.4f TpE %0.4f" % (
                            self.updates, metrics_log, t.interval, astsizes, t.interval * 1e3 / astsizes, t.interval / n_batch))
                self.logger.log(epoch=self.epochs, updates=self.updates, **dict(metrics_zip), **grads)
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
        pred_accuracies, lids_accuracies, lids_precisions, lids_recalls = [], [], [], []
        metrics_names = ["loss", "acc"]
        oldmask = self.args.mask
        self.args.mask = False
        if self.args.lids:
            metrics_names.extend(["acc_lids", "precision", "recall"])

        for minibatch in tqdm(iter_data(data, shuffle = False, size = n_batch), total = n_train // n_batch, ncols = 80, leave = False):
            with Timer() as t:
                loss, *accuracies, astsizes = self.forward(minibatch)
            losses.append(loss.data)
            pred_accuracies.append(accuracies[0])
            if self.args.lids:
                lids_accuracies.append(accuracies[1])
                lids_precisions.append(accuracies[2])
                lids_recalls.append(accuracies[3])
            metrics = [loss.data, *accuracies]
            metrics_zip = list(zip(metrics_names, tostr(metrics)))
            metrics_log = " ".join(["%s %s" % (name, val) for (name, val) in metrics_zip])
            tqdm.write("Update %d %s Interval %.4f TpE %0.4f" %
                       (updates, metrics_log, t.interval, t.interval / len(minibatch)))

        self.args.mask = oldmask
        loss = float(np.mean(losses))
        accuracy = float(np.mean(pred_accuracies))
        self.best_loss = min(self.best_loss, loss)
        self.best_accuracy = max(self.best_accuracy, accuracy)
        metrics = [loss, accuracy]

        if self.args.lids:
            lids_accuracy = float(np.mean(lids_accuracies))
            lids_precision = float(np.mean(lids_precisions))
            lids_recall = float(np.mean(lids_recalls))
            self.best_lids_accuracy = max(self.best_lids_accuracy, lids_accuracy)
            metrics.extend([lids_accuracy, lids_precision, lids_recall])

        metrics_zip = list(zip(metrics_names, tostr(metrics)))
        metrics_log = " ".join(["%s %s" % (name, val) for (name, val) in metrics_zip])
        tqdm.write("Epoch %d Updates %d %s" % (self.epochs, self.updates, metrics_log))
        self.vallogger.log(epoch=epochs, updates=updates, best_loss="%0.4f" % self.best_loss,
                           best_acc="%0.4f" % self.best_accuracy, **dict(metrics_zip))
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
#     def infer(self, tacst_test):
#         preds = []
#         for idx, (tactr_id, tacst_pt) in enumerate(tacst_test):
#             torun_logits, torun_labels = [], []
#             folder = self.tacst_folder[tactr_id]
#             folder.reset()
#             torun_logits += [folder.fold_tacst(tacst_pt.tacst)]
#             torun_labels += [0]
#             res = folder.apply(torun_logits, torun_labels)
#             logits = res[0].data.numpy()
#             preds += [np.argmax(logits)]
#             print("Logits", logits, "Predicted", np.argmax(logits), "Actual", tacst_pt.subtr_bin)
#         return preds


# -------------------------------------------------
# Debugging helper

# class ChkPosEvalTrainer(object):
#     def __init__(self, trainer1, trainer2):
#         assert isinstance(trainer1, PosEvalTrainer)
#         assert isinstance(trainer2, PosEvalTrainer)
#
#         self.trainer1 = trainer1
#         self.trainer1.f_dbg = True
#         self.trainer2 = trainer2
#         self.trainer2.f_dbg = True
#
#     def check(self):
#         losses1 = self.trainer1.train(epochs=1)
#         losses2 = self.trainer2.train(epochs=1)
#         print("Losses1: ", losses1)
#         print("Losses2: ", losses2)
#         diff = [l1 - l2 for l1, l2 in zip(losses1, losses2)]
#         print("Diff: ", diff)
        # print(all(map(lambda x: x < 0.001, diff)))
