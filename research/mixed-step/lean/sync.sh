#!/bin/bash
# copy the mixed-step Lean development from the build tree into the research repo (record)
rsync -a --delete --include='*/' --include='*.lean' --exclude='*' \
  /home/user/lean-env/qrh/Submissions/arvi_mixed_step/ /home/user/QuasiRiemannTracker/research/mixed-step/lean/arvi_mixed_step/
