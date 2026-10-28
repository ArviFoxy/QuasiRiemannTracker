#!/usr/bin/env bash
# Regenerate PR 86 steps with gen_hybrid.py in the scratch namespace QRH.ArviDensityLab and compile
# them in Lean, strictly one Lean process at a time.
#
#   run_lean_check.sh                 # steps 01 23 46 -> $LAB/Gen_NN.lean (+ Gen_Test.lean), timed
#   STEPS="12 16" run_lean_check.sh   # other steps (installed in $LAB too)
#   STEPS=all INSTALL=0 run_lean_check.sh   # all 46, compiled from $WORK only (nothing installed in $LAB)
#
# Needs: Lean 4.34.1 (PATH below), the built Lake project $QRH (PR 83 + PR 86 oleans).
set -euo pipefail
export PATH=/home/user/lean-env/lean-4.34.1-linux/bin:$PATH
HERE=$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)            # research/density
QRH=${QRH:-/home/user/lean-env/qrh}
LAB=$QRH/Submissions/arvi_density_lab/Source
SRC=$QRH/Submissions/density_split_fine_chain/Source
OL=${OLEAN_DIR:-/tmp/arvi_density_lab_olean}     # scratch .olean output; keeps .lake/build untouched
WORK=${WORK:-/tmp/arvi_density_lab_work}
STEPS=${STEPS:-"01 23 46"}
INSTALL=${INSTALL:-1}
[ "$STEPS" = all ] && STEPS=$(seq -f '%02g' 1 46)
mkdir -p "$LAB" "$WORK" "$OL/Submissions/arvi_density_lab/Source"
# Lean resolves `Submissions.*` in the FIRST search-path entry that has a Submissions/ directory,
# so the scratch oleans live in an overlay whose Submissions/ links to the real build tree.
for d in $(ls "$QRH/.lake/build/lib/lean/Submissions"); do
  [ -e "$OL/Submissions/$d" ] || ln -s "$QRH/.lake/build/lib/lean/Submissions/$d" "$OL/Submissions/$d"
done
TIMEFORMAT='%R s wall'
lean_in_qrh() {   # run lean (inside `lake env`, scratch oleans first); show its output; keep its exit status
  local out status
  out=$(cd "$QRH" && lake env bash -c "LEAN_PATH=$OL:\$LEAN_PATH lean $*" 2>&1) && status=0 || status=$?
  printf '%s\n' "$out" | grep -v '^warning: \(PrimeNumberTheoremAnd\|rellich\)' || true
  return $status
}
for i in $STEPS; do
  if [ "$INSTALL" = 1 ]; then
    python3 "$HERE/gen_hybrid.py" --from-header "$SRC/HybridK15_$i.lean" --namespace QRH.ArviDensityLab \
      --module "Gen_$i" -o "$LAB/Gen_$i.lean" -q
    echo -n "Gen_$i (installed in $LAB): "
    time lean_in_qrh -o "$OL/Submissions/arvi_density_lab/Source/Gen_$i.olean" \
         -i "$OL/Submissions/arvi_density_lab/Source/Gen_$i.ilean" "Submissions/arvi_density_lab/Source/Gen_$i.lean"
  else
    python3 "$HERE/gen_hybrid.py" --from-header "$SRC/HybridK15_$i.lean" --namespace QRH.ArviDensityLab \
      --module "Gen_$i" -o "$WORK/Gen_$i.lean" -q
    echo -n "Gen_$i ($WORK): "
    time lean_in_qrh "$WORK/Gen_$i.lean"
  fi
done
if [ "$INSTALL" = 1 ]; then
  cp "$HERE/lean_check/Gen_Test.lean" "$LAB/Gen_Test.lean"
  echo -n "Gen_Test (type identity with PR 86 + K15.density_step): "
  time lean_in_qrh "Submissions/arvi_density_lab/Source/Gen_Test.lean"
fi
