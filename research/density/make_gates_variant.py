#!/usr/bin/env python3
"""Make a copy of PR 83's `HybridGates.lean` with another density-floor numeral (and namespace).

The gate `q_floor` of `HybridGates` is `dens - 13/20`; the numeral occurs in three places of the Lean
source (the definition `gQFloor`, its clearing lemma `gQFloor_mul`, and `HybridGates.dens_floor`) plus
comments.  To certify steps with a lower floor, copy the file with this script, give the copy its own
namespace (so that it can coexist with PR 83's), and run `gen_hybrid.py` with

    --floor P/Q --gates-import <module of the copy> --gates-namespace <the new namespace>

`lean_model_check.py COPY --floor P/Q` then confirms (without Lean) that the copy and the Python gate
library agree.  NOTE: PR 83's downstream analytic files (`Density/*.lean`) consume
`QRH.SilDensitySplit.HybridGates` and hard-code the clip `[13/20, 3/4]`; they are NOT changed here.

Usage: make_gates_variant.py --floor 3/5 --namespace QRH.ArviDensityLab.F60 -o HybridGatesF60.lean
"""
import argparse
import re
import sys
from fractions import Fraction as Fr

DEFAULT_SRC = "/home/user/lean-env/qrh/Submissions/sil_density_split_20261026/Source/HybridGates.lean"
OLD = Fr(13, 20)


def make_variant(src_text: str, floor: Fr, namespace: str, old_namespace: str = "QRH.SilDensitySplit") -> str:
    p, q = floor.numerator, floor.denominator
    new_sp = f"{p} / {q}"
    new_ns = f"{p}/{q}"
    t = src_text
    counts = {}

    def sub(pattern, repl, name, expect):
        nonlocal t
        t, n = re.subn(pattern, repl, t)
        counts[name] = n
        if n != expect:
            raise SystemExit(f"expected {expect} occurrence(s) of {name}, found {n}; is this PR 83's HybridGates.lean?")

    sub(r"(def gQFloor [^\n]*:= dens B0 L0 L A D v - )13 / 20", rf"\g<1>{new_sp}", "gQFloor def", 1)
    sub(r"(densK L0 A - )13 / 20( \* densE B0 L0 L A D v)", rf"\g<1>{new_sp}\g<2>", "gQFloor_mul", 1)
    sub(r"(\) : )13 / 20( < dens B0 L0 L A D v)", rf"\g<1>{new_sp}\g<2>", "dens_floor", 1)
    t, n = re.subn(r"13/20", new_ns, t)
    counts["comments 13/20"] = n
    if re.search(r"13 ?/ ?20", t):
        raise SystemExit("a remaining occurrence of 13/20 was not replaced")
    t, n = re.subn(rf"(namespace |end ){re.escape(old_namespace)}\b", rf"\g<1>{namespace}", t)
    counts["namespace lines"] = n
    if n != 2:
        raise SystemExit(f"expected 2 namespace lines, found {n}")
    first_nl = t.index("\n")
    note = (f"DERIVED COPY of PR 83's HybridGates.lean (make_gates_variant.py): density floor 13/20 replaced "
            f"by {new_ns}; namespace {old_namespace} renamed to {namespace}.")
    t = t[:first_nl + 1] + note + "\n" + t[first_nl + 1:]
    return t


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--src", default=DEFAULT_SRC)
    ap.add_argument("--floor", type=Fr, required=True)
    ap.add_argument("--namespace", required=True, help="new Lean namespace of the copy")
    ap.add_argument("-o", "--output", required=True)
    a = ap.parse_args()
    txt = make_variant(open(a.src, encoding="utf-8").read(), a.floor, a.namespace)
    open(a.output, "w", encoding="utf-8").write(txt)
    print(f"wrote {a.output}: floor {a.floor}, namespace {a.namespace}", file=sys.stderr)


if __name__ == "__main__":
    main()
