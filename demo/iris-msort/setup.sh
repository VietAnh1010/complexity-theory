#!/usr/bin/env bash
# Fetch and build the pinned dependency stack for this demo.
#
#   Coq 8.18            (system; on Ubuntu 24.04: apt-get install coq)
#   coq-stdpp @ cafd7113
#   Iris      @ 48162f10
#   iris-time-proofs @ ce6fccb   -- Mevel/Jourdan/Pottier, time credits
#
# stdpp and Iris are installed into Coq's user-contrib (needs write access
# there); iris-time-proofs is built in place and referenced from _CoqProject.
# Only its Examples.vo target is built: the union-find and thunk files need
# coq-tlc, which this demo does not use.
set -euo pipefail

here="$(cd "$(dirname "$0")" && pwd)"
deps="$here/_deps"
jobs="$(nproc)"
mkdir -p "$deps"

clone() { # url dir commit
  [ -d "$2/.git" ] || git clone -q "$1" "$2"
  git -C "$2" fetch -q origin
  git -C "$2" checkout -q "$3"
}

clone https://gitlab.mpi-sws.org/iris/stdpp.git            "$deps/stdpp"            cafd7113
clone https://gitlab.mpi-sws.org/iris/iris.git             "$deps/iris"             48162f10
clone https://gitlab.inria.fr/gmevel/iris-time-proofs.git  "$deps/iris-time-proofs" ce6fccb

make -C "$deps/stdpp" -j"$jobs"
make -C "$deps/stdpp" install
make -C "$deps/iris" -j"$jobs"
make -C "$deps/iris" install
make -C "$deps/iris-time-proofs" -j"$jobs" theories/Examples.vo

make -C "$here" -j"$jobs"
