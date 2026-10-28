#!/usr/bin/env python3
"""Validate `gen_hybrid.py` against the 46 step files of PR 86 (`Source/HybridK15_NN.lean`).

For every step NN the parameters (B0, L0, c0, B, L, c, A, D) are read from the file's header, the
file is regenerated with `gen_hybrid.generate`, and two independent comparisons are made:

(1) structural: the exact Python objects of the generator (cleared numerator/denominator `n`, `d`
    of each of the 14 gates, the Bernstein boxes [lo, hi], their coefficient lists, `m`, `M`, the
    box reserve and the gate reserve) against the same data PARSED from PR 86's Lean text;
(2) textual: the body of the regenerated file (everything after the header comment) against the
    body of PR 86's file, byte for byte.

Usage:  validate_pr86.py [--src DIR] [--only 1,23,46] [--write DIR]
Exit status 0 iff every step passes both comparisons.
"""
import argparse
import os
import re
import sys
import time
from fractions import Fraction as Fr

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_hybrid as G  # noqa: E402

DEFAULT_SRC = "/home/user/lean-env/qrh/Submissions/density_split_fine_chain/Source"
LM_DEFAULT = "/home/user/lean-env/qrh/Submissions/sil_density_split_20261026/Source/HybridGates.lean"

REAL = re.compile(r"\(\(?(-?\d+)\)?(?: / (\d+))? : ℝ\)")


def real_list(s):
    return [Fr(int(m.group(1)), int(m.group(2)) if m.group(2) else 1) for m in REAL.finditer(s)]


def parse_poly(rhs):
    """`(a : ℝ) + (b : ℝ) * v + (c : ℝ) * v ^ 2` -> G.Poly."""
    co = {}
    for t in rhs.strip().split(" + "):
        m = re.fullmatch(r"(\(\(?-?\d+\)?(?: / \d+)? : ℝ\))(?: \* v(?: \^ (\d+))?)?", t.strip())
        assert m, t
        c = real_list(m.group(1))[0]
        p = 0 if " * v" not in t else (int(m.group(2)) if m.group(2) else 1)
        co[p] = c
    return G.Poly([co.get(i, Fr(0)) for i in range(max(co) + 1)])


def parse_gate(body):
    d = {}
    mn = re.search(r"^def n(\w+) \((?:_v|v) : ℝ\) : ℝ := (.*)$", body, re.M)
    md = re.search(r"^def d(\w+) \((?:_v|v) : ℝ\) : ℝ := (.*)$", body, re.M)
    d["short"], d["n"], d["d"] = mn.group(1), parse_poly(mn.group(2)), parse_poly(md.group(2))
    boxes = []
    pat = (r"^theorem %s\w+_bern(\d+) \(t : ℝ\) : %s\w+ \(\((.*?) : ℝ\) \+ \(\((.*?) : ℝ\) - "
           r"\((.*?) : ℝ\)\) \* t\) = (bern\d) (.*) t := by$")
    for mb in re.finditer(pat % ("n", "n"), body, re.M):
        boxes.append(dict(lo=Fr(mb.group(2).replace(" ", "")), hi=Fr(mb.group(3).replace(" ", "")),
                          nb=real_list(mb.group(6)), ndeg=int(mb.group(5)[4:])))
    for mb in re.finditer(pat % ("d", "d"), body, re.M):
        k = int(mb.group(1))
        boxes[k]["db"] = real_list(mb.group(6))
        boxes[k]["ddeg"] = int(mb.group(5)[4:])
    for mb in re.finditer(r"^theorem box\w+_(\d+) \(v : ℝ\) .*:\n    \((.*?) : ℝ\) ≤ g", body, re.M):
        boxes[int(mb.group(1))]["r"] = Fr(mb.group(2).replace(" ", ""))
    ms = re.findall(r"\(m := \((.*?) : ℝ\)\) \(M := \((.*?) : ℝ\)\)", body)
    ds = re.findall(r"\(0 : ℝ\) < \((.*?) : ℝ\)\)", body)
    for k, (m, M) in enumerate(ms):
        boxes[k]["m"], boxes[k]["M"] = Fr(m.replace(" ", "")), Fr(M.replace(" ", ""))
        boxes[k]["dmin"] = Fr(ds[k].replace(" ", ""))
    d["boxes"] = boxes
    mu = re.search(r"^theorem unif\w+ : UnifPos .*\n  refine ⟨\((.*?) : ℝ\), by norm_num", body, re.M)
    d["unif"] = Fr(mu.group(1).replace(" ", ""))
    return d


def parse_file(txt):
    parts = re.split(r"/-! #### Gate `([A-Za-z_]+)` -/", txt)
    return {parts[i]: parse_gate(parts[i + 1]) for i in range(1, len(parts), 2)}


def body_of(txt):
    return txt[txt.index("-/\n") + 3:]


def compare_structure(res, ref_gates):
    """Python objects of the generator vs. data parsed from PR 86's Lean text."""
    errs, npoly, nbox = [], 0, 0
    if [c.gate.key for c in res.certs] != list(ref_gates):
        errs.append("gate list/order differs")
        return errs, npoly, nbox
    for c in res.certs:
        r = ref_gates[c.gate.key]
        npoly += 2
        if c.n != r["n"]:
            errs.append(f"{c.gate.key}: numerator polynomial differs")
        if c.d != r["d"]:
            errs.append(f"{c.gate.key}: denominator polynomial differs")
        if len(c.boxes) != len(r["boxes"]):
            errs.append(f"{c.gate.key}: {len(c.boxes)} boxes vs {len(r['boxes'])}")
            continue
        for k, (b, rb) in enumerate(zip(c.boxes, r["boxes"])):
            nbox += 1
            mine = (b.lo, b.hi, b.nb, b.db, b.m, b.M, b.dmin, b.r, c.n.deg, c.d.deg)
            theirs = (rb["lo"], rb["hi"], rb["nb"], rb["db"], rb["m"], rb["M"], rb["dmin"], rb["r"],
                      rb["ndeg"], rb["ddeg"])
            if mine != theirs:
                errs.append(f"{c.gate.key}: box {k} differs")
        if c.r != r["unif"]:
            errs.append(f"{c.gate.key}: gate reserve differs")
    return errs, npoly, nbox


def _block(lines, i):
    """Line i and the indented continuation lines after it."""
    out = [lines[i]]
    for ln in lines[i + 1:]:
        if ln.startswith(" "):
            out.append(ln)
        else:
            break
    return "\n".join(out)


def check_aux_bernstein(gates_file):
    """The generator's local Bernstein lemmas (used for degrees > 4) must be PR 83's `bern2..bern4`
    definitions and proofs (whitespace-normalised, `lbern` -> `bern`): the pattern then extends to N > 4."""
    norm = lambda t: " ".join(t.split())
    src = open(gates_file, encoding="utf-8").read().split("\n")
    errs = []
    for N in (2, 3, 4):
        gen = G.aux_bernstein_lean(N).replace("lbern", "bern").split("\n")
        for pat in (f"def bern{N} ", f"theorem bern{N}_ge ", f"theorem bern{N}_le "):
            a = next(i for i, ln in enumerate(src) if ln.startswith(pat))
            b = next(i for i, ln in enumerate(gen) if ln.startswith(pat))
            ta, tb = _block(src, a), _block(gen, b)
            if pat.startswith("theorem"):          # compare the proofs (statements use section variables)
                ta, tb = ta.split(":= by", 1)[1], tb.split(":= by", 1)[1]
            if norm(ta) != norm(tb):
                errs.append(f"{pat.strip()}: generated text differs from PR 83")
    return errs


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--src", default=DEFAULT_SRC, help="directory with HybridK15_NN.lean")
    ap.add_argument("--only", help="comma list of step numbers (default 1..46)")
    ap.add_argument("--write", metavar="DIR", help="also write the regenerated files here")
    ap.add_argument("--gates-file", default=os.environ.get("HYBRIDGATES_LEAN", LM_DEFAULT),
                    help="PR 83's HybridGates.lean, for the Lean-source cross-check")
    a = ap.parse_args()
    steps = [int(x) for x in a.only.split(",")] if a.only else list(range(1, 47))
    if a.write:
        os.makedirs(a.write, exist_ok=True)
    t0 = time.time()
    tot_poly = tot_box = n_ident = n_struct = 0
    prev_child = None
    bad = []
    print(f"{'step':>4} {'boxes(HighAtQ)':>14} {'all boxes':>9}  structure  text")
    for i in steps:
        path = f"{a.src}/HybridK15_{i:02d}.lean"
        ref_txt = open(path, encoding="utf-8").read()
        P = G.params_from_header(path)
        res = G.generate(P, namespace="QRH.SilDensitySplit", module=f"HybridK15_{i:02d}")
        if a.write:
            with open(os.path.join(a.write, f"HybridK15_{i:02d}.lean"), "w", encoding="utf-8") as f:
                f.write(res.text)
        errs, npoly, nbox = compare_structure(res, parse_file(ref_txt))
        tot_poly += npoly
        tot_box += nbox
        same_text = body_of(ref_txt) == body_of(res.text)
        n_struct += not errs
        n_ident += same_text
        chain_ok = prev_child is None or prev_child == (P.B0, P.L0)
        prev_child = (P.B, P.L)
        print(f"{i:4d} {res.box_counts['high_at_q']:14d} {sum(res.box_counts.values()):9d}  "
              f"{'ok' if not errs else 'FAIL':9s}  {'identical' if same_text else 'DIFFERENT'}"
              f"{'' if chain_ok else '  (parent != previous child)'}")
        if errs or not same_text:
            bad.append(i)
            for e in errs[:5]:
                print("      ", e)
            if not same_text:
                x, y = body_of(ref_txt).split("\n"), body_of(res.text).split("\n")
                for k, (p, q) in enumerate(zip(x, y)):
                    if p != q:
                        print(f"       first text difference at body line {k}:\n         PR86: {p[:160]}\n"
                              f"         gen : {q[:160]}")
                        break
    n = len(steps)
    print(f"\n{n_struct}/{n} steps structurally identical ({tot_poly} cleared polynomials, {tot_box} "
          f"Bernstein boxes compared exactly); {n_ident}/{n} regenerated bodies byte-identical to PR 86; "
          f"{time.time() - t0:.1f}s")
    # (3) the Python gate library against PR 83's Lean source (definitions, _mul lemmas, structure fields)
    import lean_model_check as LM
    errs = LM.check_gates_file(a.gates_file, Fr(13, 20))
    if errs:
        print(f"gate library vs {a.gates_file}: MISMATCH")
        for e in errs:
            print("   -", e)
    else:
        print(f"gate library vs {a.gates_file}: OK (14 gate functions, 14 _mul lemmas, structure fields)")
    aux_errs = check_aux_bernstein(a.gates_file)
    print("local Bernstein lemma generator vs PR 83's bern2..bern4 (definitions and proofs): "
          + ("identical" if not aux_errs else "DIFFERENT " + "; ".join(aux_errs)))
    return 1 if (bad or errs or aux_errs) else 0


if __name__ == "__main__":
    sys.exit(main())
