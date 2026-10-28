#!/usr/bin/env bash
# Regenerate the baseline `Return/` of the package `Submissions.arvi_density` with gen_return86.py (PR 86's constants,
# PR 86's cover, two-source endpoint with both sources = PR 86's final face), build it together with the `ReturnD/` fork it
# imports (at most 2 Lean processes at a time) and compile Return_Test.lean (the endpoint fed by PR 86's chain).
#
#   run_return_check.sh              # validate (Python), regenerate, build (logs in $LOGDIR), test
#   REGEN=0 run_return_check.sh      # only build and test
set -euo pipefail
export PATH=/home/user/lean-env/lean-4.34.1-linux/bin:$PATH
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)            # research/density
ROOT=$(cd "$HERE/../.." && pwd)                                    # repository root
QRH=${QRH:-/home/user/lean-env/qrh}
PKG=$QRH/Submissions/arvi_density
LOGDIR=${LOGDIR:-/tmp/return_check_logs}
REGEN=${REGEN:-1}
if [ "$REGEN" = 1 ]; then
  python3 "$HERE/gen_return86.py" "$PKG/Return" --preset pr86 --pkg Submissions.arvi_density --ns QRH.ArviDensity --cover pr86 --clean
  python3 "$HERE/validate_return86.py" "$PKG/Return"
fi
QRH_PKG=Submissions.arvi_density python3 "$ROOT/research/mixed-step/build/build_roots.py" 2 "$LOGDIR" \
  Submissions.arvi_density.Return.Endpoint
(cd "$QRH" && time lake env lean "$HERE/lean_check/Return_Test.lean")
