#!/bin/bash
# Regenerate the final return of the mixed-step proof (ReturnD/ and FinalReturn/ of the package
# $QRH_PKG, return_cut.env) from the exact faces, and install it into the Lake project.
# See REGENERATE.md. Only files whose content changes are rewritten, so unchanged modules keep
# their build; .lean files of the package that the generators no longer emit are removed.
# usage: regenerate.sh WORKDIR        (WORKDIR: a new scratch directory for the generators' output)
# The parameters come from return_cut.env, or from the env file named by QRH_ENV (e.g. return_cut_a.env).
set -euo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
source "${QRH_ENV:-$HERE/return_cut.env}"
RM=/home/user/QuasiRiemannTracker/research/repeated-marks
LAKE=/home/user/lean-env/qrh
DEST=$LAKE/Submissions/${QRH_PKG#Submissions.}
W=$1
[ -e "$W" ] && { echo "WORKDIR $W exists" >&2; exit 1; }
mkdir -p "$W"
echo "faces: $QRH_FACES ($(sha256sum "$QRH_FACES" | cut -c1-16))"
# 0. the faces as the list [C, P] that gen_return_lean.py indexes (0 = count face, 1 = physical face)
python3 -c "import sys, json; sys.path.insert(0, '$HERE'); import theta_star as T
json.dump(T.face_list(sys.argv[1]), open(sys.argv[2], 'w'), indent=1)" "$QRH_FACES" "$W/faces.json"
# the face caps (of countGlobal and physicalGlobal) are those of the faces file
read -r CAPC CAPP < <(python3 -c "import json, sys; F = json.load(open(sys.argv[1])); print(F[0]['cap'], F[1]['cap'])" "$W/faces.json")
echo "theta $QRH_THETA, h $QRH_H, face caps $CAPC $CAPP, windows ${QRH_WINDOWS:-collet}"
cd "$RM"
# 1. exact receipts and covers; constants, row and admission certificates (FinalReturn/Rows)
python3 gen_return_lean.py "$W/faces.json" "$QRH_THETA" "$QRH_H" 0 1 "$W/RET" "$QRH_SC" "$QRH_SP" "$QRH_MODE"
# 2. Collet's final-stage modules re-instantiated with these constants (Lemma D, relaxed transport)
python3 fork_return.py "$W/RET" "$W/OUT" "$CAPC" "$CAPP" "$QRH_SC" "$QRH_SP" transport
# 3. Collet's transport layer and generic physical return against Geometry.BoundsR (QRH_RELAXED),
#    numerator cap := SP, schedule field dMinus_lower : QRH_DMINUS < dMinus
python3 fork_transport.py "$W/RD" "$QRH_SP"
# 4. assemble: ReturnD (module prefix renamed to the package), FinalReturn (forked + generated)
A=$W/PKG
mkdir -p "$A/FinalReturn"
cp -r "$W/RD/ReturnD" "$A/ReturnD"
cp "$W/OUT/FinalReturn/"*.lean "$A/FinalReturn/"
cp -r "$W/RET/FinalReturn/Rows" "$W/RET/FinalReturn/"Return{Constants,Formulas,Facts}.lean "$A/FinalReturn/"
find "$A" -name '*.lean' -exec sed -i "s/Submissions\.repeated_marks_20261024\./$QRH_PKG./g" {} +
# 5. single stage (as PR 76): the endpoint needs only the baseline's beta <= 7/8 (PR 76's Graph.NaturalCap)
python3 "$HERE/single_stage.py" "$A/FinalReturn" "$QRH_PKG" "$QRH_PR76"
! grep -rl 'repeated_marks_20261024' "$A" || { echo "unrenamed module prefix" >&2; exit 1; }
# 6. install into the Lake project
cd "$A"
new=0; same=0
while read -r f; do
  mkdir -p "$DEST/$(dirname "$f")"
  if cmp -s "$f" "$DEST/$f"; then same=$((same+1)); else cp "$f" "$DEST/$f"; new=$((new+1)); fi
done < <(find . -name '*.lean' | sed 's|^\./||' | sort)
if [ -d "$DEST" ]; then
  (cd "$DEST" && find ReturnD FinalReturn -name '*.lean' | sort) | while read -r f; do
    [ -e "$A/$f" ] || { echo "removing stale $f"; rm "$DEST/$f"; }
  done
fi
echo "installed $(find . -name '*.lean' | wc -l) modules into $DEST ($new written, $same unchanged)"
