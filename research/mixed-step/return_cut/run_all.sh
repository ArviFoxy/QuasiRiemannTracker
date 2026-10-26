#!/bin/bash
# Full rerun of the final return of the mixed-step proof (REGENERATE.md): exact theta* check,
# regeneration and installation of ReturnD/ and FinalReturn/, incremental build (2 Lean processes),
# then the axiom and constant check.   usage: run_all.sh WORKDIR   (WORKDIR: a new scratch directory)
# QRH_ENV selects the env file (default return_cut.env, design (b); return_cut_a.env is the fallback (a)).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "${QRH_ENV:-$HERE/return_cut.env}"
W=$1
t0=$(date +%s)
python3 "$HERE/theta_star.py"
"$HERE/regenerate.sh" "$W"
python3 "$HERE/build.py" 2 "$W/logs" | tee "$W/build.out"
grep -q '^ALL-OK' "$W/build.out"
python3 "$HERE/axioms_check.py" > "$HERE/AxiomsCheck.lean"
cd /home/user/lean-env/qrh
PATH=/home/user/lean-env/lean-4.34.1-linux/bin:$PATH lake env lean "$HERE/AxiomsCheck.lean" | tee "$W/axioms.out"
echo "total $(( $(date +%s) - t0 ))s"
