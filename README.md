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
2. IMPORTANT: set your terminal to point to the built version of coq
   ```
   source myconfig.sh
   ```
3. Build mathematical components and Feit-Thompson
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

TODO(deh): clean up utils


# Other

TODO(deh): missing requirements.txt
