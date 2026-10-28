#!/bin/bash
# Re-runs every verification script of the R1 study and collects the output in results.txt.
# Usage:  bash run_all.sh        (about 6-8 minutes on one core; numpy + mpmath required)
cd "$(dirname "$0")"
export PYTHONDONTWRITEBYTECODE=1
{
for s in t0_basics e12_cross_dilation e34_vanishing_pools e4_pools e5_other e6_gauss_structure e7_wholecolumn e8_large_primes e9_jacobi e10_misc e11_bidilation table_gen v_final highprec; do
  echo "################################################################  $s.py"
  python3 $s.py
  echo
done
} 2>&1 | tee results.txt
