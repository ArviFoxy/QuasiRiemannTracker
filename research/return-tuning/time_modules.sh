#!/bin/bash
# CPU (user+sys) seconds of `lake env lean FILE` for the new modules and for the originals they replace.
# Read-only: elaborates each file against the existing oleans and writes nothing.
export PATH=/home/user/lean-env/lean-4.34.1-linux/bin:$PATH
cd /home/user/lean-env/qrh
OUT=${1:-times.tsv}
: > "$OUT"
t() {
  local f=$1
  local s=$( { /usr/bin/env bash -c "TIMEFORMAT='%U %S'; time lake env lean $f >/dev/null 2>&1" ; } 2>&1 | tail -1 )
  local u=$(echo $s | awk '{print $1+$2}')
  echo -e "$f\t$u\t$(stat -c %s $f)" >> "$OUT"
}
N=Submissions/arvi_return_tuning
O=Submissions/arvi_density/Return
for m in Poly2 GuardsQ Guards Data RowsQ CoverQ Windows FinalWindows FinalScheme FinalEnvelopeBounds EdgeCertificates FinalRows FinalSchedule EndpointFromSources Endpoint FinalF50 Compat; do t $N/$m.lean; done
for f in $O/Rows/*.lean; do t $f; done
for m in Windows FinalWindows FinalScheme FinalEnvelopeBounds EdgeCertificates FinalRows FinalSchedule EndpointFromSources Endpoint; do t $O/$m.lean; done
echo DONE >> "$OUT"
