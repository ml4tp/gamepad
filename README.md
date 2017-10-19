# Directory Structure

coq, mathcomp-1.6.1, and mathcomp-odd-order-1.6.1 come from different repos.

```
+ coq (modified version of coq)
+ mathcomp-1.6.1 (ssreflect stuff)
+ mathcomp-odd-order-1.6.1 (feit-thompson)
+ notes (notes for ourselves)
+ utils (right now, just python tools for preprocessing)
```


# Initial Setup

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
   mv math-comp mathcomp-odd-order-1.6.1
   git checkout tags/mathcomp-1.6.1
   ```
3. Get Mathcomp-odd-order-1.6.1
   ```
   git clone https://github.com/math-comp/math-comp.git
   mv math-comp mathcomp-1.6.1
   git checkout tags/mathcomp-odd-order.1.6.1
   ```

Build Coq:
1. Configure coq first. (see MYHACK.md for my settings)
2. Build coq, mathematical components, and feit-thompson
   ```
   ./build_mycoq.sh
   ```

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
