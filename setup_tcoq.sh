#!/usr/bin/env bash

pushd tcoq
  echo "Configuring Coq..."
  make clean
  mkdir build
  ./configure -prefix build
  sh myconfig.sh
popd
