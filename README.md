# GamePad: A learning environemnt for theorem proving
GamePad is a Python library that exposes parts of the Coq ITP to enable machine learning. 

## Representing Coq proofs
We expose the proof trace obtained from Coq as Python data structures, including Coq’s mid-level and kernel-level term languages, proof states, proof steps, and proof trees so that they can be manipulated with arbitrary Python code. 

## Lightweight interaction 
The API provides a thin wrapper around coqtop, the Coq repl, which can be used to interactively construct proof scripts from within Python. This component mediates all interaction with Coq, including proof state parsing into GamePad’s representation of Coq proofs and sending tactic actions

For more infromation, check out the associated paper [GamePad: A Learning Environment for Theorem Proving](www.google.com)

To cite this repository in publications:

# Directory Structure

coq, mathcomp-1.6.1, and mathcomp-odd-order-1.6.1 come from different repos.

```
+ examples (example coq tactic scripts and their corresponding traces) 
+ gamepad (python learning environment for coq proofs)
+ ssreflect (patch for ssreflect)
+ tcoq (modified version of coq)
+ odd-order (feit-thompson coq repo)
+ math-comp (ssreflect coq repo)
```

# Initial Setup

1. Get the data script.
   ```
   ./get_data.sh
   ```
   This gets tcoq, math-comp, and odd-order.


# Build

Note: In order to build tcoq, make sure you use OCaml 4.05.0. It does not work with OCaml 4.06.0. You may need to run:

   ```
   opam switch 4.05.0
   opam install camlp4
   opam install ocamlfind
   ```

Build dataset:
1. Configure coq first.
   ```
   ./setup_tcoq.sh
   ```
2. Build everything
   ```
   . ./build_all.sh
   ```

Step 2 above can be broken down into:
1. Build coq next.
   ```
   ./build_tcoq.sh
   ```
2. IMPORTANT: set your terminal to point to the built version of tcoq (by setting right PATH)
   ```
   source build_config.sh
   ```
3. Patch mathematical components SSreflect
   ```
   patch math-comp/mathcomp/ssreflect.ml4 ssreflect/ssreflect.ml4.patch
   ```
4. Build mathematical components and Feit-Thompson
   ```
   ./build_mathcomp.sh; ./build_oddorder.sh
   ```



# Recurrent Building

1. Get latest changes
   ```
   git submodule update --remote --merge
   ```
2. Build (takes like 2.5 hours)
   ```
   ./build_all.sh
   ```


# Usage

* To begin, run 'chunk.py` to break up the odd-order's build.log
   ```
   python chunk.py <path-to-odd-order-build.log> <output-directory>
   ```
   We recommend having a top-level `data` folder and setting `<output-directory> = data/odd-order`.

* You you can use 'visualize.py` to visualize the tactic traces. This will attempt to reconstruct the tactic traces and record relevant statistics. Here are some example invocations:
   1. Visualize a file, saving raw tactic (before attempting to reconstruct trace) statistics to `log/rawtac.log` and outputing reconstruction statistics to `log/recon.log`. Omitting `-s` and/or `-o` means that these logs will be written to `./rawtac.log` and `./recon.log` respectively.
      ```
      python utils/visualize.py data/odd-order/BGsection1.v.dump -s log/rawtac.log -o log/recon.log
      ```
   2. Visualize the lemma `minnormal_solvable_Fitting_center` within the file and display (`-d`) the tactic trace.
      ```
      python utils/visualize.py data/odd-order/BGsection1.v.dump -l minnormal_solvable_Fitting_center -d
      ``` 
