#!/bin/sh
# Q2 lever pricing (ODE limit, all-on).  scenario list: (variant floor)
for sc in "d2 0.60" "d1 0.60" "a 0.50" "b1 0.55"; do
  set -- $sc
  python3 levers.py $1 $2 1 1.0 dR eps c6 dL0 dBP ret > logs/lev_$1_f$2.log 2>&1
done
