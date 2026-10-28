#!/bin/bash
# re-run the key scripts and keep their outputs in ../logs
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
for s in q1_base q1_scan q1_variants q1_bind rows_check adm_check xcheck_ours q2_basic q2_capP q2_full q2_guards bind_report ladder cheap_levers cap_scan levers_price floor_table floor_sweep s0_scale sens2; do
  echo "== $s"; python3 $s.py > ../logs/$s.log 2>&1
done
cp ../chain_single_all.log ../logs/ 2>/dev/null
echo ALLDONE > ../logs/ALLDONE
