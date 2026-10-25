#!/bin/bash
# Copy the combined proof from the Lake project into the upstream submission layout:
#   DEST/metadata.json, DEST/src/Candidate/Main.lean, DEST/src/Submissions/arvi_repeated_marks_on_sil_face_20261025/
# usage: package.sh LAKE_PROJECT DEST
set -euo pipefail
LAKE=$1; DEST=$2
HERE=$(cd "$(dirname "$0")" && pwd)
PKG=arvi_repeated_marks_on_sil_face_20261025
rm -rf "${DEST:?}/src"
mkdir -p "$DEST/src/Candidate" "$DEST/src/Submissions"
cp -r "$LAKE/Submissions/$PKG" "$DEST/src/Submissions/$PKG"
cp "$LAKE/Candidate/SilFace.lean" "$DEST/src/Candidate/Main.lean"
cp "$HERE/arvi-repeated-marks-on-sil-face-20261025/metadata.json" "$DEST/metadata.json" 2>/dev/null || true
find "$DEST/src" -name '*.lean' | wc -l
