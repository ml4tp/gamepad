pushd my-coq
  echo "Building Coq..."
#  make clean
  (time (make -j4 > build.log; make install)) 2> time.log
popd

pushd mathcomp-1.6.1/mathcomp
  echo "Building Mathematical Components..."
  make clean
  (time (make -j4 > build.log; make install)) 2> time.log
popd 

pushd mathcomp-odd-order-1.6.1/mathcomp
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
