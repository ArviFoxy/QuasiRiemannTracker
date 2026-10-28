#!/usr/bin/env bash
# Regenerate the two marked step certificates of the package `Submissions.arvi_density` with
# `gen_hybrid.py --marked` (floor 3/5) and build them, `MarkedStepTheorem` (which applies them to
# `Density.density_step_marked`, `#print axioms`) and everything they import, at most 2 Lean processes at a time.
#
#   run_marked_check.sh              # regenerate, build (logs in $LOGDIR)
#   REGEN=0 run_marked_check.sh      # only build
#
#   HybridMarkedK15_46       PR 86's transition 46, marked HIGH gate (A = 1/2, D = 5713/250)
#   HybridMarkedStretch46    same parent, B lowered by 3/10000 and A = 2/5: the unmarked gate `high_at_q` is
#                            negative at v = 0 (-0.0045), the marked HIGH gate holds
set -euo pipefail
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)            # research/density
ROOT=$(cd "$HERE/../.." && pwd)                                    # repository root
QRH=${QRH:-/home/user/lean-env/qrh}
PKG=$QRH/Submissions/arvi_density
SRC=$QRH/Submissions/density_split_fine_chain/Source
LOGDIR=${LOGDIR:-/tmp/marked_check_logs}
REGEN=${REGEN:-1}
if [ "$REGEN" = 1 ]; then
  python3 "$HERE/gen_hybrid.py" --from-header "$SRC/HybridK15_46.lean" --floor 3/5 --marked \
    --namespace QRH.ArviDensity --module HybridMarkedK15_46 \
    --title "density transition 46 of the k15 chain (PR 86), certified with the marked HIGH gate" \
    -o "$PKG/Source/HybridMarkedK15_46.lean"
  python3 "$HERE/gen_hybrid.py" --B0 4945703/5000000 --L0 5866251/2500000 --c0 1/10 \
    --B 4944203/5000000 --L 4683001/2000000 --c 1/10 --A 2/5 --D 5713/250 --floor 3/5 --marked \
    --namespace QRH.ArviDensity --module HybridMarkedStretch46 \
    --title "a stretched transition from the parent of PR 86's transition 46 (B lowered by 3/10000, A = 2/5; the unmarked gate high_at_q is negative at v = 0, the marked HIGH gate holds)" \
    -o "$PKG/Source/HybridMarkedStretch46.lean"
fi
QRH_PKG=Submissions.arvi_density python3 "$ROOT/research/mixed-step/build/build_roots.py" 2 "$LOGDIR" \
  Submissions.arvi_density.MarkedStepTheorem
echo "axioms:"; grep -h "depends on axioms" "$LOGDIR/Submissions.arvi_density.MarkedStepTheorem.log" || true
