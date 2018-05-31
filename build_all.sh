#!/usr/bin/env bash

. ./build_tcoq.sh
patch math-comp/mathcomp/ssreflect/plugin/v8.6/ssreflect.ml4 ssreflect/ssreflect.ml4.patch
. ./build_mathcomp.sh
. ./build_oddorder.sh
