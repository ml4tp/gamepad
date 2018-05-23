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


## Usage: Old

* You you can use 'visualize.py` to visualize the tactic traces. This will attempt to reconstruct the tactic traces and record relevant statistics. Here are some example invocations:
   1. Visualize a file, saving raw tactic (before attempting to reconstruct trace) statistics to `log/rawtac.log` and outputing reconstruction statistics to `log/recon.log`. Omitting `-s` and/or `-o` means that these logs will be written to `./rawtac.log` and `./recon.log` respectively.
      ```
      python utils/visualize.py data/odd-order/BGsection1.v.dump -s log/rawtac.log -o log/recon.log
      ```
   2. Visualize the lemma `minnormal_solvable_Fitting_center` within the file and display (`-d`) the tactic trace.
      ```
      python utils/visualize.py data/odd-order/BGsection1.v.dump -l minnormal_solvable_Fitting_center -d
      ``` 
