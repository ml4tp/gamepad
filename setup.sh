#!/usr/bin/env bash

# Get modified version of coq (probably should call tcoq for traced coq)
git submodule add https://github.com/prafullasd/tcoq.git
git submodule init
git submodule update --remote --merge

# Get mathcomp release 1.6.1
git clone https://github.com/math-comp/math-comp.git
pushd math-comp
  git checkout tags/mathcomp-1.6.1
popd

# Get odd-order release 1.6.1
git clone https://github.com/math-comp/math-comp.git odd-order
pushd odd-order
  git checkout tags/mathcomp-odd-order.1.6.1
popd

