import argparse
import math
import time

import torch
import torch.autograd as autograd
import torch.optim as optim
import torch.nn as nn

import pytorch_tools.torchfold as ptf


"""
[Note]:

Goal is to test out pytorch_tools.torchfold tool

1. A Fold() takes a tree-like structure and accumulates nodes
2. A Model works on Variable and tensor exclusively
3. Fold().apply(model, [node, label]) runs the nodes 

Options:
-m=0 gives simple model
-m=1 gives complicated model

-b sets batch to true
"""


# ---------------------------------------------------------
# AST

class Tree(object):
    def __init__(self, key):
        self.key = key


class Leaf(Tree):
    def __init__(self, key, value):
        super().__init__(key)
        self.value = value


class Child(Tree):
    def __init__(self, key, left, right):
        assert isinstance(left, Tree)
        assert isinstance(right, Tree)
        super().__init__(key)
        self.left = left
        self.right = right


class Child3(Tree):
    def __init__(self, key, left, middle, right):
        assert isinstance(left, Tree)
        assert isinstance(middle, Tree)
        assert isinstance(right, Tree)
        super().__init__(key)
        self.left = left
        self.middle = middle
        self.right = right


# ---------------------------------------------------------
# Fold + Simple Model


def embed_func(args):
    if len(args) == 1:
        return args[0].sigmoid()
    else:
        acc = autograd.Variable(torch.zeros(args[0].size()))
        for x in args:
            acc += x
        return acc.sigmoid()


class MyFolderSimp(object):
    def __init__(self, model, size):
        self.model = model
        self.size = size
        self.shared = {}
        self.folder = ptf.Fold()

    def encode(self, tree):
        # Tree -> Variable + ptf.Node
        # Add ptf.node
        encoding = self.dfs(tree)
        return self.folder.add('logits', encoding)

    def _add(self, key, *args):
        node = self.folder.add('ast_node', *args)
        self.shared[key] = node
        return node

    def dfs(self, tree):
        # Tree -> Variable + ptf.Node
        if tree.key in self.shared:
            return self.shared[tree.key]

        if isinstance(tree, Leaf):
            # Add an autograd variable
            t_id = autograd.Variable(torch.LongTensor([tree.value]))
            ev = self.model.embeddings(t_id)
            return self._add(tree.key, ev)
        elif isinstance(tree, Child):
            # Add ptf.node
            left = self.dfs(tree.left)
            right = self.dfs(tree.right)
            return self._add(tree.key, left, right)
        elif isinstance(tree, Child3):
            left = self.dfs(tree.left)
            middle = self.dfs(tree.middle)
            right = self.dfs(tree.right)
            return self._add(tree.key, left, middle, right)

    def reset(self):
        self.shared = {}
        self.folder = ptf.Fold()


class MyModelSimp(nn.Module):
    def __init__(self, num_classes, size, num_const):
        super().__init__()
        self.num_classes = num_classes
        self.size = size
        self.num_const = num_const

        self.embeddings = nn.Embedding(num_const, size)
        self.out = nn.Linear(size, num_classes)

    def ast_node(self, *args):
        return embed_func(args)

    def logits(self, encoding):
        # Type: Variable -> Variable
        return self.out(encoding)


if __name__ == "__main__":
    # Setup command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-s", "--share", type=int, default=1,
                           help="Sharing and how many minibatches before reset")
    args = argparser.parse_args()

    # Set seed for debug
    torch.manual_seed(0)

    # Create data
    t1 = Leaf(0, 0)
    t2 = Leaf(1, 1)
    t3 = Child(2, t1, t2)
    t4 = Child3(3, t1, t3, t2)
    t5 = Child3(4, t4, t2, t1)
    t6 = Child(5, t3, t2)

    # Batch expressions and literal/compound (batch size 2)
    batches = [[(t1, 0), (t3, 1)], [(t4, 1), (t2, 0)], [(t5, 1), (t6, 1)]]

    # Create model and optimizer
    num_classes = 2
    size = 10
    num_const = 2
    model = MyModelSimp(num_classes, size, num_const)
    folder = MyFolderSimp(model, size)
    criterion = nn.CrossEntropyLoss()
    opt = optim.Adam(model.parameters(), lr=0.01)
    # opt = optim.Adam(model.parameters(), lr=0.0)

    # Outer training loop
    for epoch in range(10):
        start = time.time()
        iteration = 0
        
        print("Start epoch ...", epoch)
        # Inner batch training loop
        for batch_idx, batch in enumerate(batches):
            opt.zero_grad()
            if batch_idx % args.share == 0:
                print("Resetting sharing")
                folder.reset()

            # folder = MyFolderSimp(model, size, sharer)
            all_logits, all_labels = [], []
            for tree, label in batch:
                all_logits += [folder.encode(tree)]
                all_labels += [label]
            res = folder.folder.apply(model, [all_logits, all_labels])
            loss = criterion(res[0], res[1])

            loss.backward(retain_graph=True); opt.step()

            iteration += 1
            print("Avg. Time: %fs" % ((time.time() - start) / iteration))
        print("Loss: ", loss)
