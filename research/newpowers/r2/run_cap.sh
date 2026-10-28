#!/bin/sh
# capacity-limited doubled mass: chain + exact discrete pricing, for several absolute per-step capacities UD (log_U units)
# (v=0 limit of the LOW density fixed: the doubled part counts there too; earlier numbers from the unfixed script were discarded)
cd "$(dirname "$0")"
for ud in ${UDS:-0.000003 0.00001 0.00003 0.0001}; do
  if [ ! -s results/dch_cap_$ud.log ] || ! grep -q "INFEASIBLE\|L=2.0015" results/dch_cap_$ud.log; then
    UD=$ud python3 dchain_cap.py 1.0 6.0 1.0 0.60 2.00 results/dch_cap_$ud.json > results/dch_cap_$ud.log 2>&1
  fi
  python3 eval_discrete.py results/dch_cap_$ud.json 0 >> results/cap_eval.log 2>&1
done
