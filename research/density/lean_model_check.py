#!/usr/bin/env python3
"""Cross-check the Python gate library of `gen_hybrid.py` against a Lean `HybridGates.lean` source.

No Lean process is needed.  The Lean file is read as text; the small arithmetic fragment it uses
(`def f (a b : ℝ) : ℝ := <expr in + - * / ^, numerals, applications>`) is evaluated exactly with
`fractions.Fraction`.  For every gate of `gen_hybrid.GATES` (or a list you pass) it checks, at
several random rational parameter points,

  1. definition   : the Lean gate function `gQLower ...` equals the Python `Gate.value`;
  2. `_mul` lemma : the Lean statement `g * Dg = Ng` is a true identity, and its `Dg`, `Ng` are
                    proportional to the Python `Gate.cleared` pair (what the generated
                    `clearedX` proof `Ng * d = n * Dg` needs);
  3. structure    : the field `key : UnifPos (g args) 0 (c - cross B0 L0 B L)` of `HybridGates`
                    exists with the gate function and argument list the Python gate declares,
                    and the set of `HybridGates` fields is exactly (gate keys) + (non-interval
                    fields of `STRUCT_PREAMBLE`).

So after editing a gate (in Lean or in Python), or after changing the floor numeral in a copy of
`HybridGates.lean`, a mismatch is reported here instead of by a failed `ring` inside Lean.

Usage:  lean_model_check.py [HybridGates.lean] [--floor 13/20]
"""
from __future__ import annotations

import argparse
import re
import sys
from fractions import Fraction as Fr
from typing import Dict, List, Sequence, Tuple

import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gen_hybrid as G  # noqa: E402

DEFAULT_GATES_FILE = "/home/user/lean-env/qrh/Submissions/sil_density_split_20261026/Source/HybridGates.lean"

# ---------------------------------------------------------------------------------------------
# Text handling
# ---------------------------------------------------------------------------------------------


def strip_comments(txt: str) -> str:
    txt = re.sub(r"/-.*?-/", "", txt, flags=re.S)
    return re.sub(r"--[^\n]*", "", txt)


_CMD = re.compile(r"^(?=(?:def|theorem|lemma|structure|namespace|end|section|variable|open|import|"
                  r"set_option|noncomputable|instance|abbrev|private|protected|@\[))", re.M)


def commands(txt: str) -> List[str]:
    idx = [m.start() for m in _CMD.finditer(txt)] + [len(txt)]
    return [txt[a:b].strip() for a, b in zip(idx, idx[1:])]


def match_close(s: str, i: int) -> int:
    """Index of the bracket closing the one opening at s[i]."""
    pairs = {"(": ")", "{": "}", "[": "]"}
    st = [pairs[s[i]]]
    j = i + 1
    while j < len(s) and st:
        if s[j] in pairs:
            st.append(pairs[s[j]])
        elif s[j] == st[-1]:
            st.pop()
        j += 1
    return j - 1


def split_top(s: str, sep: str) -> List[str]:
    out, depth, cur, i = [], 0, "", 0
    while i < len(s):
        if s[i] in "([{":
            depth += 1
        elif s[i] in ")]}":
            depth -= 1
        if depth == 0 and s.startswith(sep, i):
            out.append(cur)
            cur = ""
            i += len(sep)
            continue
        cur += s[i]
        i += 1
    out.append(cur)
    return out


# ---------------------------------------------------------------------------------------------
# Expression parser / evaluator for the arithmetic fragment
# ---------------------------------------------------------------------------------------------

_TOK = re.compile(r"\s*(?:(\d+(?:\.\d+)?)|([A-Za-z_Ͱ-Ͽ][A-Za-z0-9_'Ͱ-Ͽ₀-₉]*)|(.))")


def tokenize(s: str) -> List[Tuple[str, str]]:
    toks, pos = [], 0
    s = s.strip()
    while pos < len(s):
        m = _TOK.match(s, pos)
        if not m:
            break
        pos = m.end()
        if m.group(1) is not None:
            toks.append(("num", m.group(1)))
        elif m.group(2) is not None:
            toks.append(("id", m.group(2)))
        else:
            toks.append(("op", m.group(3)))
    return toks


class Parser:
    def __init__(self, s: str):
        self.t = tokenize(s)
        self.i = 0
        self.src = s
        self.ast = self.expr()
        if self.i != len(self.t):
            raise SyntaxError(f"trailing tokens {self.t[self.i:]} in {s!r}")

    def peek(self):
        return self.t[self.i] if self.i < len(self.t) else (None, None)

    def eat(self, op):
        k, v = self.peek()
        if k == "op" and v == op:
            self.i += 1
            return True
        return False

    def expr(self):
        a = self.mul()
        while True:
            if self.eat("+"):
                a = ("bin", "+", a, self.mul())
            elif self.eat("-"):
                a = ("bin", "-", a, self.mul())
            else:
                return a

    def mul(self):
        a = self.pow()
        while True:
            if self.eat("*"):
                a = ("bin", "*", a, self.pow())
            elif self.eat("/"):
                a = ("bin", "/", a, self.pow())
            else:
                return a

    def pow(self):
        a = self.unary()
        if self.eat("^"):
            return ("bin", "^", a, self.pow())
        return a

    def unary(self):
        if self.eat("-"):
            return ("neg", self.unary())
        return self.app()

    def app(self):
        head = self.atom()
        args = []
        while True:
            k, v = self.peek()
            if k in ("num", "id") or (k == "op" and v == "("):
                args.append(self.atom())
            else:
                break
        if args:
            if head[0] != "var":
                raise SyntaxError(f"application of a non-identifier in {self.src!r}")
            return ("app", head[1], args)
        return head

    def atom(self):
        k, v = self.peek()
        if k == "num":
            self.i += 1
            return ("num", Fr(v))
        if k == "id":
            self.i += 1
            return ("var", v)
        if k == "op" and v == "(":
            self.i += 1
            e = self.expr()
            if not self.eat(")"):
                raise SyntaxError(f"missing ) in {self.src!r}")
            return e
        raise SyntaxError(f"unexpected token {k}:{v} in {self.src!r}")


class LeanModel:
    def __init__(self, path: str):
        txt = strip_comments(open(path, encoding="utf-8").read())
        self.defs: Dict[str, Tuple[List[str], tuple]] = {}
        self.thms: Dict[str, Tuple[str, str]] = {}
        self.fields: Dict[str, str] = {}
        for c in commands(txt):
            if c.startswith("def "):
                m = re.match(r"def\s+(\S+)\s+((?:\([^()]*:\s*ℝ\)\s*)+):\s*ℝ\s*:=\s*(.*)$", c, re.S)
                if m:
                    names = [n for g in re.findall(r"\(([^()]*):\s*ℝ\)", m.group(2)) for n in g.split()]
                    try:
                        self.defs[m.group(1)] = (names, Parser(m.group(3)).ast)
                    except SyntaxError:
                        pass   # outside the arithmetic fragment (e.g. `max`, `if`): only gates using it fail
            elif c.startswith("theorem "):
                self._theorem(c)
            elif c.startswith("structure HybridGates"):
                self._structure(c)

    def _theorem(self, c: str):
        m = re.match(r"theorem\s+(\S+)\s*", c)
        name, i = m.group(1), m.end()
        while i < len(c) and c[i] in "({[":
            i = match_close(c, i) + 1
            while i < len(c) and c[i].isspace():
                i += 1
        if c[i:i + 1] != ":":
            return
        stmt = c[i + 1:]
        k = stmt.find(":=")
        stmt = stmt[:k] if k >= 0 else stmt
        parts = split_top(stmt, "=")
        if len(parts) == 2 and "≠" not in stmt and "≤" not in stmt and "<" not in stmt:
            self.thms[name] = (parts[0].strip(), parts[1].strip())

    def _structure(self, c: str):
        body = c.split(" where", 1)[1] if " where" in c else c
        for m in re.finditer(r"^  (\w+) : (.*?)(?=^  \w+ :|\Z)", body, re.M | re.S):
            self.fields[m.group(1)] = " ".join(m.group(2).split())

    def eval(self, ast, env: Dict[str, Fr]) -> Fr:
        k = ast[0]
        if k == "num":
            return ast[1]
        if k == "var":
            if ast[1] in env:
                return env[ast[1]]
            if ast[1] in self.defs and not self.defs[ast[1]][0]:
                return self.eval(self.defs[ast[1]][1], {})
            raise KeyError(f"unbound identifier {ast[1]}")
        if k == "neg":
            return -self.eval(ast[1], env)
        if k == "app":
            names, body = self.defs[ast[1]]
            args = [self.eval(a, env) for a in ast[2]]
            if len(args) != len(names):
                raise TypeError(f"{ast[1]} expects {len(names)} arguments, got {len(args)}")
            return self.eval(body, dict(zip(names, args)))
        op, a, b = ast[1], self.eval(ast[2], env), self.eval(ast[3], env)
        if op == "+":
            return a + b
        if op == "-":
            return a - b
        if op == "*":
            return a * b
        if op == "/":
            return a / b
        if op == "^":
            assert b.denominator == 1 and b >= 0
            return a ** int(b)
        raise ValueError(op)

    def eval_text(self, s: str, env: Dict[str, Fr]) -> Fr:
        return self.eval(Parser(s).ast, env)


def factors(ast) -> list:
    """Flatten a left-nested product into its factors."""
    if ast[0] == "bin" and ast[1] == "*":
        return factors(ast[2]) + [ast[3]]
    return [ast]


# ---------------------------------------------------------------------------------------------
# The checks
# ---------------------------------------------------------------------------------------------

SAMPLES = [
    dict(B0=Fr(9, 10), L0=Fr(5, 2), c0=Fr(1, 7), B=Fr(7, 8), L=Fr(12, 5), c=Fr(1, 10), A=Fr(3, 5),
         D=Fr(37, 3)),
    dict(B0=Fr(99999, 100000), L0=Fr(5143, 2000), c0=Fr(1397, 10000), B=Fr(2499583, 2500000),
         L=Fr(5133, 2000), c=Fr(1, 10), A=Fr(606531, 1000000), D=Fr(203633, 500)),
    dict(B0=Fr(4945703, 5000000), L0=Fr(5866251, 2500000), c0=Fr(1, 10), B=Fr(9888151, 10000000),
         L=Fr(4683001, 2000000), c=Fr(1, 10), A=Fr(1, 2), D=Fr(5713, 250)),
]
VPOINTS = [Fr(0), Fr(1, 20), Fr(3, 29), Fr(1, 7), Fr(2, 11), Fr(3, 17)]


def non_interval_fields(preamble: Sequence[str]) -> List[str]:
    return [re.match(r"(\w+)", p).group(1) for p in preamble]


def _check_gate(M: LeanModel, g: G.Gate, P: "G.Params", sm: dict, extra: dict, si: int):
    """First mismatch of gate `g` at the parameter point `sm`, as a message (None if consistent)."""
    if g.lean_fn not in M.defs:
        return f"{g.key}: no `def {g.lean_fn}` found in the Lean file"
    if g.mul_lemma not in M.thms:
        return f"{g.key}: no `theorem {g.mul_lemma}` of the form `g * Dg = Ng` found"
    hint = "  (floor numeral differs? try --floor)" if g.key == "q_floor" else ""
    Ng, Dg = g.cleared(P)
    for v in VPOINTS:
        env = dict(sm, **extra, v=v)
        try:
            lean_g = M.eval(("app", g.lean_fn, [("var", a) for a in g.fn_args + ("v",)]), env)
            lhs_txt, rhs_txt = M.thms[g.mul_lemma]
            fs = factors(Parser(lhs_txt).ast)
            lean_Dg = Fr(1)
            for f in fs[1:]:
                lean_Dg *= M.eval(f, env)
            lean_Ng = M.eval_text(rhs_txt, env)
            lean_lhs = M.eval(fs[0], env) * lean_Dg
        except (KeyError, ZeroDivisionError, SyntaxError, TypeError) as e:
            return f"{g.key}: cannot evaluate the Lean text ({type(e).__name__}: {e})"
        if lean_g != g.value(P, v):
            return (f"{g.key}: Lean `{g.lean_fn}` != Python gate value "
                    f"(parameter point #{si}, v={v}){hint}")
        if lean_lhs != lean_Ng:
            return f"{g.key}: the Lean lemma `{g.mul_lemma}` is not an identity (v={v})"
        if lean_Ng * Dg(v) != Ng(v) * lean_Dg:
            return (f"{g.key}: Python cleared pair (Ng, Dg) is not proportional to the Lean lemma "
                    f"`{g.mul_lemma}` (parameter point #{si}, v={v}){hint}")
    return None


def check_gates_file(path: str, floor: Fr = Fr(13, 20), gates: Sequence[G.Gate] = G.GATES,
                     preamble: Sequence[str] = G.STRUCT_PREAMBLE, extra=None) -> List[str]:
    """Return the list of mismatches (empty = the Python gate library matches the Lean file).
    `extra`: values of further scalar parameters (name -> Fraction) that replaced/new gates use."""
    M = LeanModel(path)
    errs: List[str] = []
    extra = {k: Fr(v) for k, v in (extra or {}).items()}
    failed = set()
    for si, sm in enumerate(SAMPLES):
        P = G.Params(**sm, floor=floor, extra=extra)
        for g in gates:
            if g.key in failed:
                continue
            msg = _check_gate(M, g, P, sm, extra, si)
            if msg:
                failed.add(g.key)
                errs.append(msg)
    # structure fields
    if not M.fields:
        errs.append("structure `HybridGates` not found")
    else:
        want = set(non_interval_fields(preamble)) | {g.key for g in gates}
        have = set(M.fields)
        for f in sorted(have - want):
            errs.append(f"structure field `{f}` of HybridGates has no gate/preamble entry in Python")
        for f in sorted(want - have):
            errs.append(f"Python gate/preamble entry `{f}` is not a field of HybridGates")
        for g in gates:
            ty = M.fields.get(g.key)
            if ty is None:
                continue
            mm = re.fullmatch(r"UnifPos \((\w+)((?: \w+)*)\) 0 \(c - cross B0 L0 B L\)", ty)
            if not mm:
                errs.append(f"{g.key}: field type `{ty}` is not `UnifPos (g args) 0 (c - cross B0 L0 B L)`")
            elif mm.group(1) != g.lean_fn or tuple(mm.group(2).split()) != tuple(g.fn_args):
                errs.append(f"{g.key}: Lean field uses `{mm.group(1)}{mm.group(2)}`, Python gate declares "
                            f"`{g.lean_fn} {' '.join(g.fn_args)}`")
    return errs


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("file", nargs="?", default=DEFAULT_GATES_FILE)
    ap.add_argument("--floor", type=lambda s: Fr(s), default=Fr(13, 20))
    a = ap.parse_args(argv)
    errs = check_gates_file(a.file, a.floor)
    if errs:
        print(f"MISMATCH between gen_hybrid.py and {a.file}:")
        for e in errs:
            print("  -", e)
        return 1
    M = LeanModel(a.file)
    print(f"OK: {len(G.GATES)} gates of gen_hybrid.GATES match {a.file} "
          f"({len(M.defs)} defs, {len(M.thms)} equational lemmas, {len(M.fields)} structure fields; "
          f"floor {G.plain_frac(a.floor)}; {len(SAMPLES)} parameter points x {len(VPOINTS)} values of v)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
