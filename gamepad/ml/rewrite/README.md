## Usage

1. Generate data (this saves to ./theorems.v)
    ```
	python gamepad/ml/rewrite/simprw.py
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
    python gamepad/visualize.py -p . theorems.dump
    ```

4. Create train/test/validation split. This creates poseval.pickle in the current directory.

    ```
    python gamepad/ml/tacst_prep.py --simprw
    ```

5. Train model. This saves a log file to <path/to/mllogs/file>

    ```
    python gamepad/ml/main.py --end2end
    ```

6. Test model.

    ```
    python gamepad/ml/main.py --end2end --validate --mload <path/to/mllogs/file>
    ```


## Experiments

NIPS version:

python gamepad/ml/main.py --end2end --mload mllogs/state_128_lr_0.001_conclu_pos_0_ln_False_drop_0.0_wd_0.0_v_False_attn_False_heads_1_m__r_/2018-05-14T224446.674225.pth --validate 

simprw-2018-05-16T212811.543397.log

fully-solved 10/50
relaxed fully-solved 50/50
avg. ratio 0.157
