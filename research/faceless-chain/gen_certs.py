"""Literal data for the packed sector certificates (`Pk.decS`): for every piece, width endpoint,
special sector and Bernstein index, the polynomial `secB` computed by the packed formula and read
back at its base `X`, as Lean prints it (`#eval`, compiled code). The common denominator `Δ` of
each piece is decided by Lean from the formula's divisibility flags, as in `gen_certk.py`.

usage: QRH_K=... QRH_SIG=... QRH_PKG=... python3 gen_certs.py LAKE_DIR OUT_FILE
Writes `tag|Δ|X|literal` lines; `gen_all.py` reads them when `QRH_CS=OUT_FILE`."""
import os, sys, subprocess
from gen_certk import MIN_DELTA, PAD_PRIMES, data_factors, lean_factors, lean_nats, factor
import family2 as F2
from gen_all import SIG, M, PKG

if __name__ == "__main__":
    lake, outf = sys.argv[1], sys.argv[2]
    fam, _ = F2.build2(SIG, m=M)
    npieces = len(fam.H)
    L = [f"import {PKG}.Faceless.ScalarZ", f"import {PKG}.Faceless.Gen.Data", "",
         "open QRH.RepeatedMarks.Faceless", "",
         "def showI (q : IPoly) : String := \"[\" ++ \", \".intercalate (q.map toString) ++ \"]\"", "",
         "def litS (Δ : ℕ) (P : Piece) (b : Poly) (j : ℕ) (i : Fin 4) : String :=",
         "  let r1 := Pk.secBZ 1 Δ 1 P b j i",
         "  let X := max r1.pos1 r1.neg1 + 1",
         "  let r := Pk.secBZ X Δ 1 P b j i",
         "  (if r.ok then \"\" else \"NOTOK\") ++ toString X ++ \"|\" ++ showI (Pk.unpack X r)", ""]
    L += MIN_DELTA + [
         "/-- `Δ` is valid for a piece iff every packed sector polynomial passes its divisibility check. -/",
         "def okSec (P : Piece) (Δ : ℕ) : Bool :=",
         "  [(0 : Fin 2), 1].all fun e => [6, 7, 8].all fun j => [(0 : Fin 4), 1, 2, 3].all fun i =>",
         "    (Pk.secBZ 1 Δ 1 P (P.endP e) j i).ok", ""]
    n = 0
    for j in range(npieces):
        L.append(f"def delta{j} : ℕ := minDelta (okSec piece{j}) {lean_factors(data_factors(fam, j))} "
                 f"{lean_nats(PAD_PRIMES)}")
        for e in (0, 1):
            for s3 in range(3):
                for i in range(4):
                    tag = f"p{j}_sec_{e}_{s3}_{i}"
                    L.append(f"#eval IO.println (\"{tag}|\" ++ toString delta{j} ++ \"|\" ++ "
                             f"litS delta{j} piece{j} (piece{j}.endP {e}) ({s3} + 6) {i})")
                    n += 1
    src = os.path.join(lake, "Scratch", "ExtractCS.lean")
    os.makedirs(os.path.dirname(src), exist_ok=True)
    open(src, 'w').write("\n".join(L) + "\n")
    res = subprocess.run(["lake", "env", "lean", src], cwd=lake, capture_output=True, text=True)
    lines = [l for l in res.stdout.splitlines() if "|" in l and l.startswith("p")]
    if len(lines) != n or any("NOTOK" in l or l.split("|")[1] == "0" for l in lines):
        sys.stderr.write(res.stdout[-2000:] + res.stderr[-2000:])
        raise SystemExit(f"expected {n} good lines, got {len(lines)}")
    open(outf, 'w').write("\n".join(lines) + "\n")
    Ds = sorted({(l.split("_")[0], int(l.split("|")[1])) for l in lines})
    print("wrote", len(lines), "sector certificates; Δ", [(p, factor(D)) for p, D in Ds])
