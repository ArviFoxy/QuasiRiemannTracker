#!/bin/bash
# Probe B batch (reproduces the tables of README.md).  usage: bash run_B_batch.sh   (from this directory)
set -u
cd "$(dirname "$0")"
mkdir -p logs results
PY="python3 -I"
run() {  # name, args...
  name=$1; shift
  echo "=== $name: $*"
  ( time $PY probeB.py --out results/$name.json "$@" ) > logs/$name.log 2>&1
  tail -3 logs/$name.log
}
# main grid: required B = 3000, 6000, 12000 and up to 768000 rows-scale, m in {0.3, 0.35, 0.43, 0.5}
run B_main   --B 3000 6000 12000 24000 48000 96000 192000 384000 768000 --m 0.3 0.35 0.43 0.5 --nrep 12 --seed 11
# finer / longer windows (3m > 1 region and beyond)
run B_mext   --B 3000 12000 48000 192000 --m 0.4 0.45 0.55 0.6 --nrep 12 --seed 12
run B_mlong  --B 3000 12000 48000 --m 0.7 0.8 --nrep 6 --seed 13
# sources as in rip/zfamily.py (odd squarefree norm prime to 3)
run B_zfam   --B 3000 6000 12000 24000 48000 96000 --m 0.3 0.35 0.43 0.5 --nrep 12 --seed 14 --sources zfamily
# source-set variants at large B (zfamily.py sources; odd norm; ideal (n) squarefree incl. inert primes)
run B_zfam_big --B 192000 384000 --m 0.43 0.5 --nrep 12 --seed 22 --sources zfamily
run B_odd_big  --B 192000 --m 0.43 0.5 --nrep 12 --seed 21 --sources odd
run B_nosq_big --B 192000 384000 --m 0.43 0.5 --nrep 12 --seed 22 --sources nosq
# one more doubling of B for the two interesting windows
run B_big      --B 1536000 --m 0.43 0.5 --nrep 8 --seed 31
