## Running models
We can now train machine learning models on the generated tactr and tacst pickle files. 
1. To run a basic model for position evaluation on kernel level ast's with folding run
	```
	python gamepad/ml/main.py
	```
   To instead train on mid level ast's, and without implicit arguments, use the `--midlvl --noimp` flags.
2. To train models for tactic prediction, run
	```
	python gamepad/ml/main.py --task tac
	```

