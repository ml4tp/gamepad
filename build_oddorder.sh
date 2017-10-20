#!/usr/bin/env bash

. source myconfig.sh
pushd odd-order/mathcomp
  pushd field
    echo "Building Field..."
    make clean
    (time (make -j4 > build.log; make install)) 2> time.log
  popd
  pushd odd_order
    echo "Building Feit-Thompson..."
    make clean
    (time (make -j4 > build.log; make install)) 2> time.log
  popd
popd
