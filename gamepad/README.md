## Directory Contents

```
|- coq
|- lib
|- ml
  |- rewrite
|- pycoqtop
|- recon
|- chunk.py
|- exp_tactr_stats.py
|- visualize.py
```

Descriptions
- coq: contains Python representation of Coq data structures and parsing
- lib: library of utility classes
- ml: machine learning functionality
	- rewrite: contains simple rewrite
- pycoqtop: lightweight interaction with coqtop
- recon: reconstructs tactic trees from TCoq dump
- chunk.py: break up odd-order.log raw data into individual files
- exp_tactr_stats.py: functionality for explore tactic tree statistics
- visualize.py: generates tactic tree pickle from raw data


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
