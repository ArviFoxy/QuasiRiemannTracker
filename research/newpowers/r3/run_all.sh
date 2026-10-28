#!/bin/bash
# Reproduce every number of R3_return.md (no lake/lean).  ~10 minutes on 4 cores.
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1 QRH_K=9/2
mkdir -p logs
for s in calib needed_sizes resistor amplification_algebra more_prices joint_p1 price_tables exact_check exact_check_joint; do
  echo "== $s"; python3 $s.py > logs/$s.log 2>&1
done
echo ALLDONE
