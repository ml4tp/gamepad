## Running models
We can now train machine learning models on the generated tactr and tacst pickle files. 
1. To run a basic model for position evaluation on kernel level ast's with folding run
	```
	python gamepad/ml/main.py
	```
2. To train models for tactic prediction, run
	```
	python gamepad/ml/main.py --task tac
	```
3. To train models for tactic argument prediction, switch to the `master-lids` branch and run
	```
	python gamepad/ml/main.py --task tac --lids --weighted
	```
4. To train on mid level ast's, and without implicit arguments, use the `--midlvl --noimp` flags. 
5. To change the model, use `--lstm` or `treelstm` flags. To add dropout use `--dropout 0.1` and `--weight_dropout 0.1`

## NIPS Experiments

The dataset (tactr.pickle and tacst.pickle), training logs and model checkpoints can be found in the [Google drive folder](https://drive.google.com/drive/folders/1tdltTB1ng7SGN1JqsuOjFLCcZBdFiPrc)

