## Usage

1. Set TCOQ_DUMP
    ```
    export TCOQ_DUMP=/tmp/tcoq.log
    ```
    Also, make sure that you are using TCoq.

2. Generate data (this saves to ./theorems.v)
    ```
	python gamepad/ml/rewrite/simprw.py
    ```

3. Extract data using TCoq.
    ```
    coqc theorems.v; cp /tmp/tcoq.log theorems.dump
    ```

4. Create tactr.pickle in the current directory.
    ```
    python gamepad/visualize.py file theorems.dump -p .
    ```

5. Create train/test/validation split. This creates poseval.pickle in the current directory.
    ```
    python gamepad/ml/tacst_prep.py --simprw
    ```

6. Train model. This saves a log file to <path/to/mllogs/file>
    ```
    python gamepad/ml/main.py --simprw
    ```

7. Test model tactic prediction.
    ```
    python gamepad/ml/main.py --simprw --mload <path/to/mllogs/file> --validate
    ```
8. Run trained model end2end.
    ```
	python gamepad/ml/main.py --simprw --mload <path/to/mllogs/file> --teste2e
	```


## Experiments

NIPS version:

python gamepad/ml/main.py --end2end --mload mllogs/state_128_lr_0.001_conclu_pos_0_ln_False_drop_0.0_wd_0.0_v_False_attn_False_heads_1_m__r_/2018-05-14T224446.674225.pth --validate 

simprw-2018-05-16T212811.543397.log

fully-solved 10/50
relaxed fully-solved 50/50
avg. ratio 0.157
