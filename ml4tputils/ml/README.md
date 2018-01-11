# Steps

1. Produce tactic tree pickle file
   ```
   python ml4tputils/visualize.py -p <path-to-files>
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
   
