"""Literal data for the packed sector certificates (`Pk.decS`): for every piece, width endpoint,
special sector and Bernstein index, the polynomial `secB` computed by the packed formula and read
back at its base `X`, as Lean prints it (`#eval`, compiled code).

usage: QRH_K=... QRH_SIG=... QRH_PKG=... python3 gen_certs.py LAKE_DIR OUT_FILE
Writes `tag|Δ|X|literal` lines; `gen_all.py` reads them when `QRH_CS=OUT_FILE`."""
import os, sys, subprocess
from fractions import Fraction as Fr
from math import lcm
from gen_certk import deltas
import family2 as F2
from gen_all import SIG, M, PKG

# the sector formula's own constants (beyond the HIGH formula's): 5/6, 1/50, 1/3, 2/3, ν/2, ν/5
EXTRA = [Fr(5, 6), Fr(1, 50), Fr(1, 3), Fr(2, 3), Fr(1, 2), Fr(1, 5), Fr(1, 6)]

if __name__ == "__main__":
    lake, outf = sys.argv[1], sys.argv[2]
    fam, _ = F2.build2(SIG, m=M)
    Ds = [D for D in deltas(fam)]
    for c in EXTRA:
        Ds = [lcm(D, c.denominator) for D in Ds]
    L = [f"import {PKG}.Faceless.ScalarZ", f"import {PKG}.Faceless.Gen.Data", "",
         "open QRH.RepeatedMarks.Faceless", "",
         "def showI (q : IPoly) : String := \"[\" ++ \", \".intercalate (q.map toString) ++ \"]\"", "",
         "def litS (Δ : ℕ) (P : Piece) (b : Poly) (j : ℕ) (i : Fin 4) : String :=",
         "  let r1 := Pk.secBZ 1 Δ 1 P b j i",
         "  let X := max r1.pos1 r1.neg1 + 1",
         "  let r := Pk.secBZ X Δ 1 P b j i",
         "  (if r.ok then \"\" else \"NOTOK\") ++ toString X ++ \"|\" ++ showI (Pk.unpack X r)", ""]
    n = 0
    for j, D in enumerate(Ds):
        for e in (0, 1):
            for s3 in range(3):
                for i in range(4):
                    tag = f"p{j}_sec_{e}_{s3}_{i}"
                    L.append(f"#eval IO.println (\"{tag}|{D}|\" ++ litS {D} piece{j} (piece{j}.endP {e}) ({s3} + 6) {i})")
                    n += 1
    src = os.path.join(lake, "Scratch", "ExtractCS.lean")
    os.makedirs(os.path.dirname(src), exist_ok=True)
    open(src, 'w').write("\n".join(L) + "\n")
    res = subprocess.run(["lake", "env", "lean", src], cwd=lake, capture_output=True, text=True)
    lines = [l for l in res.stdout.splitlines() if "|" in l and l.startswith("p")]
    if len(lines) != n or any("NOTOK" in l for l in lines):
        sys.stderr.write(res.stdout[-2000:] + res.stderr[-2000:])
        raise SystemExit(f"expected {n} good lines, got {len(lines)}")
    open(outf, 'w').write("\n".join(lines) + "\n")
    print("wrote", len(lines), "sector certificates; Δ bits", [D.bit_length() for D in Ds])
