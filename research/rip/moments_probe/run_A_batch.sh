#!/bin/bash
# Probe A batch (reproduces the tables of README.md).  Needs gcc (for gauss_prime.c) and ~6 GB RAM.
# usage: bash run_A_batch.sh   (from this directory)
set -u
cd "$(dirname "$0")"
mkdir -p logs results
export MP_BUILD="${MP_BUILD:-/tmp/moments_probe_build}"
PY="python3 -I"
run() {  # name, args...
  name=$1; shift
  echo "=== $name: $*"
  ( time $PY probeA.py results/$name.npz "$@" ) > logs/$name.log 2>&1
  tail -3 logs/$name.log
}
# exact Gauss sums, the main run and its robustness variants
run A_true_lin_K20000_np10      --kmax 20000 --nprimes 10 --w lin  --gmode true
run A_true_lin_K20000_np20      --kmax 20000 --nprimes 20 --w lin  --gmode true
run A_true_sq_K20000_np10       --kmax 20000 --nprimes 10 --w sq   --gmode true
run A_true_bump_K20000_np10     --kmax 20000 --nprimes 10 --w bump --gmode true
run A_true_lin_c025_K20000_np10 --kmax 20000 --nprimes 10 --w lin  --gmode true --cscale 0.25
run A_true_lin_c4_K20000_np10   --kmax 20000 --nprimes 10 --w lin  --gmode true --cscale 4
# surrogates (null calibration): 10 replicas each, Phi shared
run A_randphase_lin_K20000_np10 --kmax 20000 --nprimes 10 --w lin --gmode randphase --nrep 10
run A_randcube_lin_K20000_np10  --kmax 20000 --nprimes 10 --w lin --gmode randcube  --nrep 10
