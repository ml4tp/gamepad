1. Generate data (this saves to ./theorems.v)
    ```
    python ml4tputils/ml/solver.py
    ```

2. Extract data using TCoq. Use the first command if TCOQ_DUMP=/tmp/tcoq.log. Use the second command otherwise.
    ```
    coqc theorems.v; cp /tmp/tcoq.log theorems.dump
    ```
    
    ```
    coqc theorems.v > theorems.dump
    ```

3. Visualize data using ML4Coq. This creates tactr.pickle in the current directory.

    ```
    python ml4tputils/visualize.py -p . theorems.dump
    ```

4. Create train/test/validation split. This creates poseval.pickle in the current directory.

    ```
    python ml4tputils/ml/tacst_prep.py --simprw
    ```

5. Train model. This saves a log file to <path/to/mllogs/file>

    ```
    python ml4tputils/ml/main.py --end2end
    ```

6. Test model.

    ```
    python ml4tputils/ml/main.py --end2end --validate --mload <path/to/mllogs/file>
    ```

