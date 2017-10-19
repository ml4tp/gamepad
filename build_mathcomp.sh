#!/usr/bin/env bash

pushd math-comp/mathcomp
  echo "Building Mathematical Components..."
  make clean
  (time (make -j4 > build.log; make install)) 2> time.log
popd
