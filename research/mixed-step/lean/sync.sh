#!/bin/bash
# copy the mixed-step Lean development from the build tree into the research repo (record)
SRC=/home/user/lean-env/qrh/Submissions/arvi_mixed_step
DST=/home/user/QuasiRiemannTracker/research/mixed-step/lean/arvi_mixed_step
rm -rf "$DST"; mkdir -p "$DST"
cd "$SRC" && find . -name '*.lean' | while read f; do mkdir -p "$DST/$(dirname "$f")"; cp "$f" "$DST/$f"; done
