## Directory Contents

```
|- coq                 (Python representation of Coq data structures and parsing)
|- lib                 (library of utility classes)
|- ml                  (machine learning functionality)
  |- rewrite           (simprw example)
|- pycoqtop            (wrapper around interaction with coqtop)
|- recon               (reconstructs tactic trees from tcoq dump)
|- chunk.py
|- exp_tactr_stats.py  (explore tactic tree statistics)
|- tactr_prep.py       (generates tactic tree pickle from raw data)
```


## Constructing Tactic Tree Data Sets


We have two ways of constructing tactic tree data sets.
1. Apply GamePad to a single Coq file.
2. Apply GamePad to a file listing Coq dump files (e.g., Feit-Thompson).


### Usage 1: Constructing tactic trees from single coq file

We start in the project root directory.
1. (OPTIONAL) Compile Coq source file with tcoq to generate dump file if you are not using Feit-Thompson data set. For instance, you can compile any of the `.v` files under `examples/`:
   ```
   coqc examples/<foo.v> > examples/foo.dump
   ```
2. Produce tactic tree pickle file:
   ```
   python gamepad/tactr_prep.py file foo.dump -p examples
   ```
   This produces `tactr.pickle` file in current working directory.
3. Prepare tactic tree pickle for machine learning:
   ```
   python gamepad/ml/tacst_prep.py
   ```
   This produces `tacst.pickle` in current working directory. It splits tactic trees into individual tactic states as well as partition the data set into train/test/validate sets.


### Usage 2: Constructing tactic trees from list of files such as Feit-Thompson

We start in the project root directory.
1. Produce tactic tree pickle file:
   ```
   python gamepad/tactr_prep.py files odd_order_files.txt -p data/odd-order
   ```
   This produces `tactr.pickle` file in current working directory.
2. Prepare tactic tree pickle for machine learning:
   ```
   python gamepad/ml/tacst_prep.py
   ```
   This produces `tacst.pickle` in current working directory. It splits tactic trees into individual tactic states as well as partition the data set into train/test/validate sets.
