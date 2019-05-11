# GamePad: A Learning Environment for Theorem Proving
GamePad is a Python library that exposes parts of the Coq ITP to enable machine learning. 


## Representing Coq Proofs

We expose the proof trace obtained from Coq as Python data structures, including Coq’s mid-level and kernel-level term languages, proof states, proof steps, and proof trees so that they can be manipulated with arbitrary Python code. 


## Lightweight Interaction 

The API provides a thin wrapper around coqtop, the Coq repl, which can be used to interactively construct proof scripts from within Python. This component mediates all interaction with Coq, including proof state parsing into GamePad’s representation of Coq proofs and sending tactic actions

For more infromation, check out the associated paper [GamePad: A Learning Environment for Theorem Proving](https://arxiv.org/abs/1806.00608). For datasets, models and results from the paper, check out the [Google drive folder](https://drive.google.com/drive/folders/1tdltTB1ng7SGN1JqsuOjFLCcZBdFiPrc)

To cite this repository in publications:
```
@article{huang2018gamepad,
  title={{GamePad: A Learning Environment for Theorem Proving}},
  author={Daniel Huang and Prafulla Dhariwal and Dawn Song and Ilya Sutskever},
  journal={arXiv preprint arXiv:1806.00608},
  year={2018},
}
```

# Directory Structure

coq, mathcomp-1.6.1, and mathcomp-odd-order-1.6.1 come from different repos.

```
|- examples   (example Coq tactic scripts and their corresponding traces) 
|- gamepad    (Python learning environment for Coq proofs)
|- ssreflect  (patch for ssreflect)
|- tcoq       ("Traced Coq", i.e., modified version of Coq; created by get_data.sh)
|- odd-order  (Feit-Thompson Coq repo; created by get_data.sh)
|- math-comp  (Ssreflect Coq repo; created by get_data.sh)
|- mllogs     (hold ml logs, will be auto-generated)
```


# Installation and Setup
 
There are three components to install and setup.
1. (REQUIRED): Install tcoq (Traced Coq) and modified Ssreflect (provides tactic language extensions). This step installs a modified version of Coq that records proof trees.
2. (OPTIONAL): Compile and extract Feit-Thompson data set. This step is optional.
3. (REQUIRED): Install the GamePad tool for visualizing and applying machine learning to Coq proofs.

To obtain the auxilliary repositories, you can run `./get_data.sh` (this obtains `tcoq`, `math-comp`, and `odd-order`).


## Requirements

1. Python3: GamePad does not support Python2.
2. OCaml 4.05.0: in order to build tcoq, make sure you use OCaml 4.05.0. It does not work with OCaml 4.06.0.
3. Coq 8.6.1: tcoq is a patch to Coq 8.6.1.


## Step 1: Build Traced Coq (TCoq) and Mathematical Components

1. Obtain the correct version of OCaml. You can use OCaml's package manager `opam`. You may need to run:
   ```
   opam switch 4.05.0
   opam install camlp4
   opam install ocamlfind
   ```
2. Configure tcoq. (Make sure to pull the tcoq submodule first, e.g., with `./get_data.sh`.)
   ```
   ./setup_tcoq.sh
   ```
3. Build tcoq. If you want extract the dumps for the Coq standard library, you will need to remove the `-j4` flag from `./build_tcoq.sh` so that the log files will be output in order.
   ```
   ./build_tcoq.sh
   ```
4. IMPORTANT: set your terminal to point to the built version of tcoq (by setting right PATH)
   ```
   source build_config.sh
   ```
5. Patch mathematical components SSreflect
   ```
   patch math-comp/mathcomp/ssreflect/plugin/v8.6/ssreflect.ml4 ssreflect/ssreflect.ml4.patch
   ```
6. Build mathematical components (i.e. ssreflect)
   ```
   ./build_mathcomp.sh
   ```


## Build Feit-Thompson Data Set

1. Check that you are using `tcoq`.
   ```
   which coqc
   ```
2. Build Feit-Thompson data set.
   ```
   ./build_oddorder.sh
   ```
3. Break up the Feit-Thompson log file.
    ```
    python chunk.py <path-to-odd-order-build.log> <output-directory>
    ```
    We recommend having a top-level `data` folder and setting `<output-directory> = data/odd-order`. For example,
    ```
    python chunk.py odd-order/mathcomp/odd_order/build.log ./data/odd-order
    ```


## Setup GamePad

As a reminder, use Python3. Change to the GamePad directory `cd gamepad`.
1. We recommend that you create a virutal environment (e.g., an environment called `gamepad3`).
    ```
    virtualenv -p python3 gamepad3
    ```
    If you have virtualenv wrapper, you can use the command below instead.
    ```
    mkvirtualenv --python=<path/to/local/python3> gamepad3
    ```
2. Install the requirements in the environment.
    ```
    pip install -r requirements.txt
    ```
3. Install the gamepad package locally as a development.
    ```
    pip install -e .
    ```


# Usage

1. Prepare and explore data sets extracted by tcoq (see gamepad/README.md)
2. Basic machine learning on tactic states (see gamepad/ml/README.md)
3. Simple rewrite example (see gamepad/ml/rewrite/README.md)
