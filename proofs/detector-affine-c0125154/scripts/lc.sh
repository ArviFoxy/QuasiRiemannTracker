#!/bin/bash
# compile one Candidate module manually: lc.sh Candidate.Affine.Arith
export PATH=/home/user/leanbuild/lean-4.34.1-linux/bin:$PATH
cd /home/user/leanbuild/project
mod=$1
rel=${mod//.//}
out=.lake/build/lib/lean/$rel
mkdir -p $(dirname $out)
lake env lean --root=/home/user/QuasiRiemannTracker/submissions/detector-affine-c0125154/src -o $out.olean -i $out.ilean /home/user/QuasiRiemannTracker/submissions/detector-affine-c0125154/src/$rel.lean 2>&1 | grep -v "^warning: \(Prime\|rellich\)"
echo "exit ${PIPESTATUS[0]}"
