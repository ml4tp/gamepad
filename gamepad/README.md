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
|- visualize.py        (generates tactic tree pickle from raw data)
```


## Setup

Use Python 3.

Run `python3 setup.py develop` inside `gamepad/`.


## Usage: Constructing Tactic Trees from TCoq Dump Files

We start in the project root directory.
1. Produce tactic tree pickle file
   ```
   coqc <path-to-coq-files> > thm.dump
   python gamepad/visualize.py -p <path-to-coq-files> thm.dump
   ```
   This produces `tactr.pickle` file in current working directory.
2. Create datasets
   ```
   python gamepad/ml/tacst_prep.py
   ```
   This produces `tacst.pickle` in current working directory.
3. Run ML
   ```
   python gamepad/ml/main.py --fold
   ```
   This trains the model on the tacst.pickle file.
