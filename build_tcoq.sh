#!/usr/bin/env bash

pushd tcoq
  echo "Building Coq..."
  # make clean
  (time (make -j4 > build.log; make install)) 2> time.log
popd
