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


## Experiments

NIPS version:

python ml4tputils/ml/main.py --end2end --mload mllogs/state_128_lr_0.001_conclu_pos_0_ln_False_drop_0.0_wd_0.0_v_False_attn_False_heads_1_m__r_/2018-05-14T224446.674225.pth --validate 

simprw-2018-05-16T212811.543397.log

fully-solved 10/50
relaxed fully-solved 50/50
avg. ratio 0.157

ICML version:

1. Command
    python ml4tputils/ml/main.py --end2end --validate --mload mllogs/state_128_lr_0.001_conclu_pos_0_ln_False_drop_0.0_wd_0.0_v_False_attn_False_heads_1_m__r_/2018-02-08T165821.717116.pth

2. Log file
    simprw.log

3. Stats
    fully-solved            : 15/50 (bad > 0)
    relaxed fully-solved    : 50/50 (num_steps in everything is 9)
    avg. ratio of bad steps : 0.12 (~1/9, or 1 step)


Refactored version:

1. Command
    python ml4tputils/ml/main.py --end2end --validate --mload mllogs/state_128_lr_0.001_conclu_pos_0_ln_False_drop_0.0_wd_0.0_v_False_attn_False_heads_1_m__r_/2018-02-20T224422.836121.pth

2. Log file
    simprw-2018-02-20T225947.445922.log

3. Stats
    fully-solved             :  13/50 (bad_steps > 0)
    relaxed fully-solved     :  50/50 (num_steps in everything is 9)
    Avg. ratio of bad steps  :  0.12 (~1/9, or 1 step)

