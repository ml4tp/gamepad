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
    def __init__(self):
        pass


class Leaf(Tree):
    def __init__(self, value):
        self.value = value


class Child(Tree):
    def __init__(self, left, right):
        assert isinstance(left, Tree)
        assert isinstance(right, Tree)
        self.left = left
        self.right = right


class Child3(Tree):
    def __init__(self, left, middle, right):
        assert isinstance(left, Tree)
        assert isinstance(middle, Tree)
        assert isinstance(right, Tree)
        self.left = left
        self.middle = middle
        self.right = right


# ---------------------------------------------------------
# Fold + Simple Model

class MyFolderSimp(object):
    def __init__(self, size):
        self.size = size
        self.folder = ptf.Fold()

    def dfs(self, tree):
        # Tree -> Variable + ptf.Node
        if isinstance(tree, Leaf):
            # Add an autograd variable
            t_id = autograd.Variable(torch.LongTensor([tree.value]))
            return self.folder.add('leaf', t_id)
        elif isinstance(tree, Child):
            # Add ptf.node
            left = self.dfs(tree.left)
            right = self.dfs(tree.right)
            return self.folder.add('child', left, right)
        elif isinstance(tree, Child3):
            left = self.dfs(tree.left)
            middle = self.dfs(tree.middle)
            right = self.dfs(tree.right)
            return self.folder.add('child3', left, middle, right)

    def encode(self, tree):
        # Tree -> Variable + ptf.Node
        # Add ptf.node
        encoding = self.dfs(tree)
        return self.folder.add('logits', encoding)


class MyModelSimp(nn.Module):
    def __init__(self, num_classes, size, num_const):
        super().__init__()
        self.num_classes = num_classes
        self.size = size
        self.num_const = num_const

        self.embeddings = nn.Embedding(num_const, size)
        self.out = nn.Linear(size, num_classes)
    
    def leaf(self, t_id):
        # Type: Variable -> Variable
        return self.embeddings(t_id)

    def child(self, t_left, t_right):
        # Type: Variable * Variable -> Variable
        return (t_left + t_right).sigmoid()

    def child3(self, t_left, t_middle, t_right):
        # Type: Variable * Variable * Variable -> Variable
        return (t_left + t_middle + t_right).sigmoid()

    def logits(self, encoding):
        # Type: Variable -> Variable
        return self.out(encoding)


# ---------------------------------------------------------
# Fold + Model

class MyFolder(object):
    def __init__(self, size, nn=None):
        self.size = size
        if nn:
            self.folder = ptf.Unfold(nn)
        else:
            self.folder = ptf.Fold()

    def dfs(self, tree):
        # Tree -> ptf.Node * ptf.Node
        if isinstance(tree, Leaf):
            return self.folder.add('leaf', tree.value).split(2)
        elif isinstance(tree, Child):
            left_h, left_c = self.dfs(tree.left)
            right_h, right_c = self.dfs(tree.right)
            return self.folder.add('child', left_h, left_c, right_h, right_c).split(2)
        elif isinstance(tree, Child3):
            left_h, left_c = self.dfs(tree.left)
            middle_h, middle_c = self.dfs(tree.middle)
            right_h, right_c = self.dfs(tree.right)
            return self.folder.add('child3', left_h, left_c, middle_h, middle_c, right_h, right_c).split(2)

    def encode(self, tree):
        # Tree -> ptf.Node
        h, c = self.dfs(tree)
        return self.folder.add('logits', h)


class MyTreeLSTM(nn.Module):
    def __init__(self, num_units):
        super().__init__()
        self.num_units = num_units
        self.left = nn.Linear(num_units, 5 * num_units)
        self.right = nn.Linear(num_units, 5 * num_units)

    def forward(self, left_in, right_in):
        lstm_in = self.left(left_in[0])
        lstm_in += self.right(right_in[0])
        a, i, f1, f2, o = lstm_in.chunk(5, 1)
        c = (a.tanh() * i.sigmoid() + f1.sigmoid() * left_in[1] +
             f2.sigmoid() * right_in[1])
        h = o.sigmoid() * c.tanh()
        return h, c


class MyModel(nn.Module):
    def __init__(self, num_classes, size, num_const):
        super().__init__()
        self.num_classes = num_classes
        self.size = size
        self.num_const = num_const

        self.tree_lstm = MyTreeLSTM(size)
        self.embeddings = nn.Embedding(num_const, size)
        self.out = nn.Linear(size, num_classes)

    def leaf(self, t_id):
        # Variable -> Variable * Variable
        # x = autograd.Variable(torch.FloatTensor(t_id.size()[0], self.size))
        x = autograd.Variable(torch.zeros(t_id.size()[0], self.size))
        return self.embeddings(t_id), x

    def child(self, left_h, left_c, right_h, right_c):
        # Variable * Variable * Variable * Variable -> Variable * Variable
        h, c = self.tree_lstm((left_h, left_c), (right_h, right_c))
        return h, c

    def child3(self, left_h, left_c, middle_h, middle_c, right_h, right_c):
        # Variable * Variable * Variable * Variable * Variable * Variable -> Variable * Variable
        h, c = self.tree_lstm((left_h, left_c), (middle_h, middle_c))
        return self.tree_lstm((h, c), (right_h, right_c))

    def logits(self, encoding):
        # Variable -> Variable
        return self.out(encoding)


if __name__ == "__main__":
    # Setup command line
    argparser = argparse.ArgumentParser()
    argparser.add_argument("-m", "--model", type=int,
                           help="Model 0, 1, 2", default=0)
    argparser.add_argument("-b", "--batch", action="store_true")
    args = argparser.parse_args()

    # Create data
    t1 = Leaf(0)
    t2 = Leaf(1)
    t3 = Child(t1, t2)
    t4 = Child3(t1, t3, t2)
    t5 = Child3(t4, t2, t1)
    t6 = Child(t3, t2)

    # Batch expressions and literal/compound (batch size 2)
    batches = [[(t1, 0), (t3, 1)], [(t4, 1), (t2, 0)], [(t5, 1), (t6, 1)]]

    # Create model and optimizer
    num_classes = 2
    size = 10
    num_const = 2
    if args.model == 0:
        model = MyModelSimp(num_classes, size, num_const)
    else:
        model = MyModel(num_classes, size, num_const)
    criterion = nn.CrossEntropyLoss()
    opt = optim.Adam(model.parameters(), lr=0.01)
    # opt = optim.Adam(model.parameters(), lr=0.0)

    # Outer training loop
    for epoch in range(10):
        start = time.time()
        iteration = 0
        
        print("START EPOCH ...", epoch)
        # Inner batch training loop
        for batch_idx, batch in enumerate(batches):
            opt.zero_grad()

            if args.model == 0:
                folder = MyFolderSimp(size)
            else:
                if args.batch:
                    folder = MyFolder(size)
                else:
                    folder = MyFolder(size, model)
                
            all_logits, all_labels = [], []
            for tree, label in batch:
                all_logits += [folder.encode(tree)]
                all_labels += [label]
            res = folder.folder.apply(model, [all_logits, all_labels])
            loss = criterion(res[0], res[1])
    
            loss.backward(); opt.step()

            iteration += 1
            print("Avg. Time: %fs" % ((time.time() - start) / iteration))
        print("Loss: ", loss)
