#!/bin/sh
# capacity-limited doubled mass: chain + exact discrete pricing, for several absolute masses UD (log_U units)
cd "$(dirname "$0")"
for ud in 0.00001 0.00003 0.0001 0.0003 0.001; do
  UD=$ud python3 dchain_cap.py 1.0 6.0 1.0 0.60 2.00 results/dch_cap_$ud.json > results/dch_cap_$ud.log 2>&1
  python3 eval_discrete.py results/dch_cap_$ud.json 14 >> results/cap_eval.log 2>&1
done
