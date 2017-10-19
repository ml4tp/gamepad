# Directory Structure

coq, mathcomp-1.6.1, and mathcomp-odd-order-1.6.1 come from different repos.

```
+ tcoq (modified version of coq)
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
   This gets tcoq, math-comp, and odd-order.


# Build

Build Coq:
1. Configure coq first.
   ```
   ./setup_tcoq.sh
   ```
2. Build coq, mathematical components, and Feit-Thompson (in this order).
   ```
   ./build_all.sh
   ```
   Note that `./build_tcoq.sh`, `./build_mathcomp.sh`, and `./build_oddorder.sh` can be used to build each of the libraries separately, but they must be build in order.


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

TODO(deh): clean up utils


# Other

TODO(deh): missing requirements.txt
