# Directory Structure

coq, mathcomp-1.6.1, and mathcomp-odd-order-1.6.1 come from different repos.

```
+ coq (modified version of coq)
+ odd-order (feit-thompson)
+ math-comp (ssreflect stuff)
+ notes (notes for ourselves)
+ utils (right now, just python tools for preprocessing)
```


# Initial Setup

1. Run the setup script.
   ```
   ./setup.sh
   ```
   This gets coq, math-comp, and odd-order.


TODO(deh): deprecated
In the root directory:
1. Get Coq
   ```
   git submodule add dan-e-huang@bitbucket.org:dan-e-huang/my-coq.git
   git submodule init
   git submodule update --remote --merge
   ```
2. Get Mathcomp-1.6.1
   ```
   git clone https://github.com/math-comp/math-comp.git
   git checkout tags/mathcomp-1.6.1
   ```
3. Get Mathcomp-odd-order-1.6.1
   ```
   git clone https://github.com/math-comp/math-comp.git odd-order
   git checkout tags/mathcomp-odd-order.1.6.1
   ```


# Build

Build Coq:
1. Configure coq first.
   ```
   ./setup_mycoq.sh
   ```
2. Build coq, mathematical components, and Feit-Thompson (in this order).
   ```
   ./build_all.sh
   ```
   Note that `./build_mycoq.sh`, `./build_mathcomp.sh`, and `./build_oddorder.sh` can be used to build each of the libraries separately, but they must be build in order.


TODO(deh): automate this
1. Get coq from repo
2. Get mathcomp-1.6.1 from public git (needs to be release version)
3. Get mathcomp-odd-order-1.6.1 from public git (needs to be release version)
  

# Recurrent Building

1. Get latest changes
   ```
   git submodule update --remote --merge
   ```
2. Build (takes like 2.5 hours)
   ```
   ./build_mycoq.sh
   ```


# Usage

TODO(deh): clean up utils


# Other

TODO(deh): missing requirements.txt
