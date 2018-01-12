# Steps

Use Python 3.

Run `python3 setup.py develop` inside `ml4tputils/`.

1. Produce tactic tree pickle file
   ```
   coqc <path-to-coq-files> thm.dump
   python ml4tputils/visualize.py -p <path-to-coq-files> thm.dump
   ```
   This produces `tactr.pickle` file in current working directory.
2. Create datasets
   ```
   python ml4tputils/ml/tacst_prep.py
   ```
   Creates `tacpred.pickle` and `poseval.pickle`
3. Run ML
   ```
   python ml4tputils/ml/main.py
   ```
   This runs the model on the tactr.pickle file.
   
