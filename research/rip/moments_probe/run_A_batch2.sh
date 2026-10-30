#!/bin/bash
# Probe A batch 2: conjugation-symmetric surrogates (null for the (P, Pbar) class) and the largest-K run.
# usage: bash run_A_batch2.sh   (from this directory); the last run needs ~8 GB RAM.
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
run A_randphasesym_lin_K20000_np10 --kmax 20000 --nprimes 10 --w lin --gmode randphasesym --nrep 10
run A_randcubesym_lin_K20000_np10  --kmax 20000 --nprimes 10 --w lin --gmode randcubesym  --nrep 10
run A_true_lin_K50000_np10         --kmax 50000 --kmin 500 --ngrid 16 --nprimes 10 --w lin --gmode true
