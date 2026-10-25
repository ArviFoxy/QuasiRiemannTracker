"""Literal data for the packed HIGH certificates (`Pk.decKgX`): for every piece, width endpoint and
branch, the 16 coefficient polynomials of `highU`, computed by the packed formula and read back, as
Lean prints them (`#eval`, compiled code), with the common denominator `Δ` of each piece.

`Δ` is decided by Lean. The packed formula's own divisibility flags (`ok`) are the only record of
which denominators occur, so no formula constant is repeated here. The valid `Δ` are exactly the
multiples of a least one (they are closed under gcd and multiples), and `minDelta` finds it by one
bisection per prime, starting from the data's denominators times high powers of small primes
(`data_factors`, padded by `minDelta`).

usage: QRH_K=... QRH_SIG=... QRH_PKG=... python3 gen_certk.py LAKE_DIR OUT_FILE
Writes `tag|Δ|X|literal` lines; `gen_all.py` reads them when `QRH_CK=OUT_FILE`."""
import os, sys, subprocess
from fractions import Fraction as Fr
from math import lcm
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'repeated-marks'))
import family2 as F2
from gen_all import SIG, M, PKG

# primes allowed in the denominators of the formula's own constants
PAD_PRIMES = (2, 3, 5, 7)

def factor(n):
    f, p = {}, 2
    while p * p <= n:
        while n % p == 0:
            f[p] = f.get(p, 0) + 1
            n //= p
        p += 1
    if n > 1:
        f[n] = f.get(n, 0) + 1
    return f

def data_factors(fam, j):
    """The common denominator of piece `j`'s data and width endpoints, factored."""
    D = 1
    for q in tuple(fam.polys(j)) + ([F2.CAPMAX],):
        for c in q:
            D = lcm(D, Fr(c).denominator)
    return sorted(factor(D).items())

def lean_factors(fs):
    return "[" + ", ".join(f"({p}, {a})" for p, a in fs) + "]"

def lean_nats(ns):
    return "[" + ", ".join(str(n) for n in ns) + "]"

# Lean, shared with gen_certs.py: the least valid `Δ` for a validity test `ok`
MIN_DELTA = [
    "def prodF (fs : List (ℕ × ℕ)) : ℕ := fs.foldl (fun acc pa => acc * pa.1 ^ pa.2) 1", "",
    "/-- `fs` with the exponents of the primes `ps` raised by `E`. -/",
    "def padF (fs : List (ℕ × ℕ)) (ps : List ℕ) (E : ℕ) : List (ℕ × ℕ) :=",
    "  let fs' := ps.foldl (fun acc p => if acc.any (·.1 == p) then acc else acc ++ [(p, 0)]) fs",
    "  fs'.map fun pa => if ps.contains pa.1 then (pa.1, pa.2 + E) else pa", "",
    "/-- The least `a ≤ hi` with `ok (rest * p ^ a)`, by bisection (`ok` is monotone in `a`). -/",
    "partial def minExp (ok : ℕ → Bool) (rest p lo hi : ℕ) : ℕ :=",
    "  if hi ≤ lo then hi else",
    "    let mid := (lo + hi) / 2",
    "    if ok (rest * p ^ mid) then minExp ok rest p lo mid else minExp ok rest p (mid + 1) hi", "",
    "/-- The least valid `Δ`. Start from the data's denominators `data`, with the small primes `ps`",
    "padded to the first valid power `16·2^i`; then lower each exponent by bisection. The valid `Δ`",
    "are exactly the multiples of the least one, so this finds it. `0` if no padding is valid. -/",
    "def minDelta (ok : ℕ → Bool) (data : List (ℕ × ℕ)) (ps : List ℕ) : ℕ :=",
    "  match (List.range 9).find? (fun i => ok (prodF (padF data ps (16 * 2 ^ i)))) with",
    "  | none => 0",
    "  | some i =>",
    "    let fs := padF data ps (16 * 2 ^ i)",
    "    prodF ((List.range fs.length).foldl (fun cur k =>",
    "      let pa := cur[k]!",
    "      cur.set k (pa.1, minExp ok (prodF (cur.eraseIdx k)) pa.1 0 pa.2)) fs)", ""]

if __name__ == "__main__":
    lake, outf = sys.argv[1], sys.argv[2]
    fam, _ = F2.build2(SIG, m=M)
    npieces = len(fam.H)
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
    L += MIN_DELTA + [
         "def branches : List QRH.RepeatedMarks.Branch := [(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2)]", "",
         "/-- `Δ` is valid for a piece iff every packed HIGH coefficient passes its divisibility check. -/",
         "def okHigh (P : Piece) (Δ : ℕ) : Bool :=",
         "  [(0 : Fin 2), 1].all fun e => branches.all fun k =>",
         "    (coeffsK 1 Δ P (P.endP e) k).all fun row => row.all (·.ok)", ""]
    for j in range(npieces):
        L.append(f"def delta{j} : ℕ := minDelta (okHigh piece{j}) {lean_factors(data_factors(fam, j))} "
                 f"{lean_nats(PAD_PRIMES)}")
        for e in (0, 1):
            for k in [(i, jj) for i in range(2) for jj in range(3)]:
                tag = f"p{j}_high_{e}_{k[0]}{k[1]}"
                L.append(f"#eval IO.println (\"{tag}|\" ++ toString delta{j} ++ \"|\" ++ "
                         f"litK delta{j} piece{j} (piece{j}.endP {e}) ({k[0]}, {k[1]}))")
    src = os.path.join(lake, "Scratch", "ExtractCK.lean")
    os.makedirs(os.path.dirname(src), exist_ok=True)
    open(src, 'w').write("\n".join(L) + "\n")
    res = subprocess.run(["lake", "env", "lean", src], cwd=lake, capture_output=True, text=True)
    lines = [l for l in res.stdout.splitlines() if "|" in l and l.startswith("p")]
    if len(lines) != 12 * npieces or any(l.split("|")[1] == "0" for l in lines):
        sys.stderr.write(res.stdout[-2000:] + res.stderr[-2000:])
        raise SystemExit(f"expected {12 * npieces} lines with a valid Δ, got {len(lines)}")
    open(outf, 'w').write("\n".join(lines) + "\n")
    Ds = sorted({(l.split("_")[0], int(l.split("|")[1])) for l in lines})
    print("wrote", len(lines), "certificates; Δ", [(p, factor(D)) for p, D in Ds])
