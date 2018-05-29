# GamePad: A Learning Environment for Theorem Proving
GamePad is a Python library that exposes parts of the Coq ITP to enable machine learning. 


## Representing Coq Proofs

We expose the proof trace obtained from Coq as Python data structures, including Coq’s mid-level and kernel-level term languages, proof states, proof steps, and proof trees so that they can be manipulated with arbitrary Python code. 


## Lightweight Interaction 

The API provides a thin wrapper around coqtop, the Coq repl, which can be used to interactively construct proof scripts from within Python. This component mediates all interaction with Coq, including proof state parsing into GamePad’s representation of Coq proofs and sending tactic actions

For more infromation, check out the associated paper [GamePad: A Learning Environment for Theorem Proving](www.google.com)

To cite this repository in publications:


# Directory Structure

coq, mathcomp-1.6.1, and mathcomp-odd-order-1.6.1 come from different repos.

```
|- examples   (example Coq tactic scripts and their corresponding traces) 
|- gamepad    (Python learning environment for Coq proofs)
|- ssreflect  (patch for ssreflect)
|- tcoq       (modified version of Coq)
|- odd-order  (Feit-Thompson Coq repo)
|- math-comp  (Ssreflect Coq repo)
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


## Step 1: Build Traced Coq (TCoq) and Mathematical Components

1. Obtain the correct version of OCaml. You can use OCaml's package manager `opam`. You may need to run:
   ```
   opam switch 4.05.0
   opam install camlp4
   opam install ocamlfind
   ```
2. Configure tcoq.
   ```
   ./setup_tcoq.sh
   ```
3. Build tcoq.
   ```
   ./build_tcoq.sh
   ```
4. IMPORTANT: set your terminal to point to the built version of tcoq (by setting right PATH)
   ```
   source build_config.sh
   ```
5. Patch mathematical components SSreflect
   ```
   patch math-comp/mathcomp/ssreflect/plugin/v8.6/ssreflect.ml4 ssreflect/ssreflect.ml4.patch2
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
   python chunk.py odd-order/mathcomp/odd_order/build.log ./data
   ```


## Setup GamePad

As a reminder, use Python3. Change to the GamePad directory `cd gamepad`.
```
pip install -r requirements.txt
```
You can also install the gamepad package locally.
Run `python setup.py develop` inside `./gamepad/`.


# Usage

1. Prepare and explore data sets extracted by tcoq (see gamepad/README.md)
2. Basic machine learning on tactic states (see gamepad/ml/README.md)
3. Simple rewrite example (see gamepad/ml/rewrite/README.md)
