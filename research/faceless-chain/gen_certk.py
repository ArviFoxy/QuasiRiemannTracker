"""Literal data for the packed HIGH certificates (`Pk.decK`): for every piece, width endpoint and
branch, the 16 coefficient polynomials of `highU`, computed by the packed formula and read back, as
Lean prints them (`#eval`, compiled code). Also the common denominator `Δ` of each piece.

usage: QRH_K=... QRH_SIG=... QRH_PKG=... python3 gen_certk.py LAKE_DIR OUT_FILE
Writes `tag|Δ|literal` lines; `gen_all.py` reads them when `QRH_CERTK=OUT_FILE`."""
import os, sys, subprocess
from fractions import Fraction as Fr
from math import lcm
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import family2 as F2
import polyq as P
from gen_all import SIG, M, PKG

def deltas(fam):
    e, r, f = F2.FEES; cap = F2.CAPMAX; den = fam.den
    out = []
    for j in range(len(fam.H)):
        B, L, B0, L0, sv = fam.polys(j)
        D = 1
        for b in (sv, [cap]):
            t = P.sub(B, P.mul(L, P.sub(b, [e])))
            Dn = P.smul(6*den, B0)
            Na = P.add(P.smul(1 - den, P.add(P.mul(L0, b), P.sub(t, B0))), P.smul(6*r, B0))
            al = P.smul(1 - den, L0); be = P.sub(P.smul(Fr(9, 2), B0), al); six = P.smul(6, B0)
            for q in (t, b, Na, Dn, B0, L0, al, be, six):
                for c in q:
                    D = lcm(D, Fr(c).denominator)
        for c in [Fr(1, 6), Fr(1, 2), e, 1 - e, 2*e, f, cap] + [2*p*cap for p in (0, 1, -1, 2)]:
            D = lcm(D, Fr(c).denominator)
        out.append(D)
    return out

if __name__ == "__main__":
    lake, outf = sys.argv[1], sys.argv[2]
    fam, _ = F2.build2(SIG, m=M)
    Ds = deltas(fam)
    L = [f"import {PKG}.Faceless.Packed", f"import {PKG}.Faceless.Gen.Data", "",
         "open QRH.RepeatedMarks.Faceless", "",
         "def showI (q : IPoly) : String := \"[\" ++ \", \".intercalate (q.map toString) ++ \"]\"", "",
         "instance : Inhabited Pk.PZ := ⟨Pk.zero⟩", "",
         "def ptIdx (x : ℚ) : Nat := if x = 0 then 0 else if x = 1 then 1 else if x = -1 then 2 else 3", "",
         "/-- `Pk.highUZ X Δ 1 P b k`, all 16 coefficients, with every intermediate value computed once. -/",
         "def coeffsK (X Δ : ℕ) (P : Piece) (b : Poly) (k : QRH.RepeatedMarks.Branch) : Array (Array Pk.PZ) :=",
         "  let pts : List ℚ := [0, 1, -1, 2]",
         "  let samples : Array (Array Pk.PZ) :=",
         "    (pts.map fun ν => (pts.map fun p => Pk.valPZ X Δ 1 P b k ν p).toArray).toArray",
         "  let f : ℚ → ℚ → Pk.PZ := fun ν p => (samples[ptIdx ν]!)[ptIdx p]!",
         "  let cA : Array (Array Pk.PZ) :=",
         "    ((List.finRange 4).map fun i => ((List.finRange 4).map fun j => Pk.bicubicZ Δ f i j).toArray).toArray",
         "  let α := Pk.ofPoly X Δ P.alphaP 1",
         "  let β := Pk.ofPoly X Δ P.betaP 1",
         "  let D := Pk.ofPoly X Δ P.sixB0P 1",
         "  ((List.finRange 4).map fun a => ((List.finRange 4).map fun j =>",
         "    Pk.cuZ Δ (fun i j => (cA[i.val]!)[j.val]!) α β D a j).toArray).toArray", "",
         "def alignK (Δ : ℕ) (c : Array (Array Pk.PZ)) : Array (Array Pk.PZ) :=",
         "  let E := c.foldl (fun acc row => row.foldl (fun acc' r => max r.e acc') acc) 0",
         "  c.map fun row => row.map fun r => Pk.scale Δ r (E - r.e)", "",
         "def litK (Δ : ℕ) (P : Piece) (b : Poly) (k : QRH.RepeatedMarks.Branch) : String :=",
         "  let a1 := alignK Δ (coeffsK 1 Δ P b k)",
         "  let X := a1.foldl (fun acc row => row.foldl (fun acc' r => max (max r.pos1 r.neg1) acc') acc) 0 + 1",
         "  let aX := alignK Δ (coeffsK X Δ P b k)",
         "  toString X ++ \"|\" ++ \"![\" ++ \", \".intercalate (aX.toList.map fun row => \"![\" ++ \", \".intercalate",
         "    (row.toList.map fun r => showI (Pk.unpack X r)) ++ \"]\") ++ \"]\"", ""]
    for j, D in enumerate(Ds):
        for e in (0, 1):
            for k in [(i, jj) for i in range(2) for jj in range(3)]:
                tag = f"p{j}_high_{e}_{k[0]}{k[1]}"
                L.append(f"#eval IO.println (\"{tag}|{D}|\" ++ litK {D} piece{j} (piece{j}.endP {e}) ({k[0]}, {k[1]}))")
    src = os.path.join(lake, "Scratch", "ExtractCK.lean")
    os.makedirs(os.path.dirname(src), exist_ok=True)
    open(src, 'w').write("\n".join(L) + "\n")
    res = subprocess.run(["lake", "env", "lean", src], cwd=lake, capture_output=True, text=True)
    lines = [l for l in res.stdout.splitlines() if "|" in l and l.startswith("p")]
    if len(lines) != 12*len(Ds):
        sys.stderr.write(res.stdout[-2000:] + res.stderr[-2000:])
        raise SystemExit(f"expected {12*len(Ds)} lines, got {len(lines)}")
    open(outf, 'w').write("\n".join(lines) + "\n")
    print("wrote", len(lines), "certificates; Δ bits", [D.bit_length() for D in Ds])
