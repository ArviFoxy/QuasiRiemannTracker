#!/usr/bin/env python3
"""Generator of Lean step-certificate files for the density-split chain (PR 83 `HybridGates`).

One generated file proves, for ONE transition G(B0,L0,c0) -> G(B,L,c) with selection constants A, D,
the structure `HybridGates B0 L0 c0 B L c A D` of PR 83 (`Source/HybridGates.lean`): every gate is
cleared to a polynomial ratio (`clearedX`, via `mul_eq_of_cleared` and the `g*_mul` lemmas), and the
numerator is proved positive on boxes of `v in [0, c - s0]`, `s0 = (B0-B)/(L0-L)`, by exact
Bernstein coefficients (`bern0`..`bern4`, `box_lower`).  The layout is PR 86's
`Source/HybridK15_NN.lean`, which follows Sil's `Source/HybridCertificatesFirst.lean`.

All arithmetic is exact (`fractions.Fraction`).  The rules below were established against the 46
PR 86 files and reproduce them byte for byte (`validate_pr86.py`):

* `n, d` of a gate are the primitive integer polynomials proportional to the cleared pair
  `(Ng, Dg)` of the gate's `_mul` lemma (multiply by the lcm of all denominators, then divide by
  the gcd of all integer coefficients);
* Bernstein degree = exact degree of the polynomial (`n` and `d` separately), on the box
  `v = lo + (hi - lo) t`;
* box rule: starting from `[0, c - s0]` a box is accepted when every Bernstein coefficient of `n`
  and of `d` is > 0, otherwise it is bisected at its midpoint (recursively, left to right);
* per box: `m = min` Bernstein coefficient of `n`, `M = max` of `d`, reserve `m/M`; the gate
  reserve is the minimum over its boxes.

Command line (see README.md):
    gen_hybrid.py --B0 99999/100000 --L0 5143/2000 --c0 1397/10000 \\
                  --B 2499583/2500000 --L 5133/2000 --c 1/10 --A 606531/1000000 --D 203633/500 \\
                  [--floor 13/20] --namespace QRH.SilDensitySplit --module HybridK15_01 -o out.lean
    gen_hybrid.py --from-header Source/HybridK15_05.lean --module HybridK15_05 -o out.lean
    gen_hybrid.py --steps steps.json --outdir DIR --module-pattern 'Gen_{i:02d}'
    gen_hybrid.py --list-gates
    gen_hybrid.py --from-header Source/HybridK15_46.lean --floor 3/5 --marked --namespace QRH.ArviDensity \\
                  --module HybridMarkedK15_46 -o out.lean        # HybridGatesM (marked HIGH gate), see below

Marked mode (`--marked`, `marked_lib`): proves `HybridGatesM qf ...` of `Submissions.arvi_density.Source.
HybridGatesMarked` (the gates above without the two unmarked HIGH gates `high_at_q`,
`high_density_derivative`, plus `high_marked`: the HIGH payment with PR 76's repeated-mark gain `gainC`).
`high_marked` is certified, for each of the six facet branches (i, j), by exact tensor Bernstein
coefficients on boxes of `(v, t, p)`, `v in [0, c - s0]`, `t in [0, 1]` (the density
`nu = q(v) + t (3/4 - q(v))`), `p in [0, 1/2]` (the amplitude class); see the section "Marked HIGH gate".

Python API:  gen_step(B0, L0, c0, B, L, c, A, D, floor, namespace, module) -> Result, or
             generate(Params(...), namespace=..., module=..., lib=PR83_LIB) -> Result
             (.text = the Lean file, .report, .summary(), .warnings, .certs = exact polynomials and boxes).
A gate is replaced with `lib.replace(key, Gate(...))` (or `--gate-lib my_lib.py`), the floor numeral is
`Params.floor` / `--floor` (the Lean side needs a matching copy of HybridGates: make_gates_variant.py;
`lean_model_check.py` / `--check-gates-file` compares the Python gates with a Lean source without Lean).
"""
from __future__ import annotations

import argparse
import json
import os
import re
import runpy
import sys
import time
from dataclasses import dataclass, field, replace
from fractions import Fraction
from functools import reduce
from math import comb, gcd
from typing import Callable, Dict, List, Optional, Sequence, Tuple

Fr = Fraction

# ----------------------------------------------------------------------------------------------
# Exact one-variable polynomials over the rationals
# ----------------------------------------------------------------------------------------------


class Poly:
    """Polynomial in `v` with Fraction coefficients (index = power), trailing zeros trimmed."""

    __slots__ = ("c",)

    def __init__(self, coeffs):
        c = [Fr(x) for x in coeffs]
        while len(c) > 1 and c[-1] == 0:
            c.pop()
        self.c = tuple(c if c else [Fr(0)])

    @property
    def deg(self) -> int:
        return len(self.c) - 1

    @staticmethod
    def _co(x) -> "Poly":
        return x if isinstance(x, Poly) else Poly([x])

    def __add__(self, o):
        o = Poly._co(o)
        n = max(len(self.c), len(o.c))
        return Poly([(self.c[i] if i < len(self.c) else 0) + (o.c[i] if i < len(o.c) else 0)
                     for i in range(n)])

    __radd__ = __add__

    def __neg__(self):
        return Poly([-x for x in self.c])

    def __sub__(self, o):
        return self + (-Poly._co(o))

    def __rsub__(self, o):
        return Poly._co(o) + (-self)

    def __mul__(self, o):
        o = Poly._co(o)
        r = [Fr(0)] * (len(self.c) + len(o.c) - 1)
        for i, a in enumerate(self.c):
            for j, b in enumerate(o.c):
                r[i + j] += a * b
        return Poly(r)

    __rmul__ = __mul__

    def __truediv__(self, s):
        s = Fr(s)
        return Poly([x / s for x in self.c])

    def __pow__(self, k: int):
        r = Poly([1])
        for _ in range(k):
            r = r * self
        return r

    def __call__(self, x) -> Fraction:
        r = Fr(0)
        for a in reversed(self.c):
            r = r * x + a
        return r

    def __eq__(self, o):
        return isinstance(o, Poly) and self.c == o.c

    def __hash__(self):
        return hash(self.c)

    def __repr__(self):
        return "Poly(%s)" % ", ".join(str(x) for x in self.c)

    def affine(self, lo, hi) -> "Poly":
        """The polynomial t |-> p(lo + (hi - lo) t)."""
        base = Poly([lo, Fr(hi) - Fr(lo)])
        out = Poly([0])
        for a in reversed(self.c):
            out = out * base + a
        return out


V = Poly([0, 1])   # the variable v


def lcm(a: int, b: int) -> int:
    return a // gcd(a, b) * b


def primitive_pair(Ng: Poly, Dg: Poly) -> Tuple[Poly, Poly]:
    """(n, d) = lambda (Ng, Dg) with integer coefficients and joint gcd 1 (lambda > 0 rational)."""
    den = 1
    for x in Ng.c + Dg.c:
        den = lcm(den, x.denominator)
    ints = [int(x * den) for x in Ng.c + Dg.c]
    g = reduce(gcd, ints)
    return (Poly([Fr(int(x * den), g) for x in Ng.c]), Poly([Fr(int(x * den), g) for x in Dg.c]))


def bernstein(p: Poly, lo, hi) -> List[Fraction]:
    """Bernstein coefficients (degree = exact degree of p) of t |-> p(lo + (hi-lo) t) on [0,1]."""
    q = p.affine(lo, hi)
    n = p.deg
    c = list(q.c) + [Fr(0)] * (n + 1 - len(q.c))
    return [sum(Fr(comb(i, j), comb(n, j)) * c[j] for j in range(i + 1)) for i in range(n + 1)]


# ----------------------------------------------------------------------------------------------
# Parameters of one transition
# ----------------------------------------------------------------------------------------------

PARAM_NAMES = ("B0", "L0", "c0", "B", "L", "c", "A", "D")


@dataclass(frozen=True)
class Params:
    B0: Fraction
    L0: Fraction
    c0: Fraction
    B: Fraction
    L: Fraction
    c: Fraction
    A: Fraction
    D: Fraction
    floor: Fraction = Fr(13, 20)      # numeral of the density-floor gate q_floor
    extra: Tuple[Tuple[str, Fraction], ...] = ()   # further scalar parameters of replaced/new gates

    def __post_init__(self):
        for k in PARAM_NAMES + ("floor",):
            object.__setattr__(self, k, Fr(getattr(self, k)))
        ex = self.extra.items() if isinstance(self.extra, dict) else self.extra
        object.__setattr__(self, "extra", tuple(sorted((str(k), Fr(v)) for k, v in ex)))

    def get(self, name: str) -> Fraction:
        """Value of a parameter by name (B0..D, floor, or an `extra` parameter)."""
        if name in PARAM_NAMES or name == "floor":
            return getattr(self, name)
        for k, v in self.extra:
            if k == name:
                return v
        raise KeyError(f"unknown parameter {name!r} (known extras: {[k for k, _ in self.extra]})")

    @property
    def s0(self) -> Fraction:
        return (self.B0 - self.B) / (self.L0 - self.L)

    @property
    def h(self) -> Fraction:
        """Right end of the excess interval [0, h], h = c - s0."""
        return self.c - self.s0

    # ---- derived exact quantities shared by the gates (names as in HybridGates.lean) ----
    @property
    def K(self) -> Fraction:
        """densK = (999/1000) L0 A"""
        return Fr(999, 1000) * self.L0 * self.A

    @property
    def X(self) -> Poly:
        """1 + D v"""
        return 1 + self.D * V

    @property
    def E(self) -> Poly:
        """densE = (L0 - L)(1 + D v) + (6 B0 - L0) A"""
        return (self.L0 - self.L) * self.X + (6 * self.B0 - self.L0) * self.A

    @property
    def F(self) -> Poly:
        """15 densE - 6 densK"""
        return 15 * self.E - 6 * self.K

    @property
    def W(self) -> Poly:
        """width = s0 + v"""
        return self.s0 + V

    def chain_step_warnings(self) -> List[str]:
        """Hypotheses of PR 86's `K15.density_step` (`Density.DSFace`, positivity) that are not part of
        `HybridGates`: a step violating them certifies but cannot be fed to `density_step`."""
        w = []
        for ok, msg in ((self.B <= self.B0, "DSFace.B_le: B <= B0"), (self.B0 < 1, "DSFace.B0_lt: B0 < 1"),
                        (self.L < self.L0, "DSFace.L_lt: L < L0"), (1 < self.L, "DSFace.one_lt_L: 1 < L"),
                        (self.c < Fr(1, 6), "DSFace.c_lt: c < 1/6"), (self.c0 < Fr(1, 6), "DSFace.c0_lt: c0 < 1/6"),
                        (0 < self.L0, "density_step: 0 < L0"), (0 < self.B0, "density_step: 0 < B0"),
                        (0 < self.c0, "density_step: 0 < c0")):
            if not ok:
                w.append(f"density_step hypothesis fails: {msg}")
        return w

    def lit(self, name: str) -> str:
        return lean_real(self.get(name))

    def lits(self) -> Dict[str, str]:
        """Lean literals of every parameter, for the `{B0}`-style placeholders of library templates."""
        d = {k: self.lit(k) for k in PARAM_NAMES}
        d.update({k: lean_real(v) for k, v in self.extra})
        d.update(floor=lean_real(self.floor), s0=lean_real(self.s0), h=lean_real(self.h))
        return d

    def check_marked_preconditions(self) -> None:
        """The marked HIGH gate uses the repeated-mark gain on its parent range (`ParentParams`,
        `density_step_marked`): 22/23 <= B0 <= 1, 1 < L0, 0 <= c0 <= 1, and 1/2 <= floor <= 3/4."""
        errs = []
        if not (Fr(22, 23) <= self.B0 <= 1):
            errs.append("22/23 <= B0 <= 1 (parent range of the repeated-mark gain)")
        if not self.L0 > 1:
            errs.append("1 < L0")
        if not (0 <= self.c0 <= 1):
            errs.append("0 <= c0 <= 1")
        if not (Fr(1, 2) <= self.floor <= Fr(3, 4)):
            errs.append("1/2 <= floor <= 3/4")
        if errs:
            raise ValueError("unsupported parameters for the marked gate: " + "; ".join(errs))

    def check_template_preconditions(self) -> None:
        """The fixed Lean scripts for `cross_eq`, `x_pos`, `E_pos`, `F_pos`, `width_pos`
        (norm_num / nlinarith) need these facts; reject parameters for which they are false."""
        errs = []
        if self.L0 - self.L <= 0:
            errs.append("L0 - L must be > 0 (cross slope s0 = (B0-B)/(L0-L))")
        if self.D < 0:
            errs.append("D must be >= 0 (x_pos: 0 < 1 + D v for v >= 0)")
        if self.L0 - self.L > 0:
            if self.h <= 0:
                errs.append("c - s0 must be > 0 (width_pos); got c - s0 = %s" % self.h)
            if self.D >= 0:
                if self.E(0) <= 0:
                    errs.append("densE(0) must be > 0 (E_pos)")
                if self.F(0) <= 0:
                    errs.append("15 densE(0) - 6 densK must be > 0 (F_pos)")
        if errs:
            raise ValueError("unsupported parameters: " + "; ".join(errs))


# ----------------------------------------------------------------------------------------------
# Lean rendering helpers
# ----------------------------------------------------------------------------------------------


def lean_real(x) -> str:
    """Lean real literal in PR 86's style: `(a / b : ℝ)`, `(a : ℝ)`, `((-a) : ℝ)`."""
    x = Fr(x)
    if x.denominator == 1:
        return f"((-{-x.numerator}) : ℝ)" if x.numerator < 0 else f"({x.numerator} : ℝ)"
    if x.numerator < 0:
        return f"(-{-x.numerator} / {x.denominator} : ℝ)"
    return f"({x.numerator} / {x.denominator} : ℝ)"


def plain_frac(x) -> str:
    x = Fr(x)
    return f"{x.numerator}/{x.denominator}" if x.denominator != 1 else f"{x.numerator}"


def lean_poly(p: Poly) -> str:
    """`(a : ℝ) + (b : ℝ) * v + (c : ℝ) * v ^ 2` (zero terms dropped)."""
    terms = []
    for k, a in enumerate(p.c):
        if a == 0 and not (k == 0 and p.deg == 0):
            continue
        if k == 0:
            terms.append(lean_real(a))
        elif k == 1:
            terms.append(f"{lean_real(a)} * v")
        else:
            terms.append(f"{lean_real(a)} * v ^ {k}")
    return " + ".join(terms)


# ---- Bernstein forms: PR 83 provides bern0..bern4; higher degrees get local `lbernN` lemmas ----

LIB_BERN_MAX = 4


def bern_fn(deg: int) -> str:
    return f"bern{deg}" if deg <= LIB_BERN_MAX else f"lbern{deg}"


def _pw(base: str, e: int) -> str:
    return "" if e == 0 else (base if e == 1 else f"{base} ^ {e}")


def _bern_term(i: int, N: int) -> str:
    c = comb(N, i)
    parts = ([] if c == 1 else [str(c)]) + [f"b{i}"]
    if i >= 1:
        parts.append(_pw("t", i))
    if N - i >= 1:
        parts.append(_pw("(1 - t)", N - i))
    return " * ".join(parts)


def aux_bernstein_lean(N: int) -> str:
    """Local Bernstein form and bound lemmas of degree N > 4, shaped exactly like PR 83's
    `bern4`, `bern4_ge`, `bern4_le`."""
    bs = " ".join(f"b{i}" for i in range(N + 1))
    nm = f"lbern{N}"
    L = [f"/-! #### Local Bernstein lemmas of degree {N} (not provided by `HybridGates`) -/", "",
         f"def {nm} ({bs} t : ℝ) : ℝ :=", "  " + " + ".join(_bern_term(i, N) for i in range(N + 1)), ""]
    for sense in ("ge", "le"):
        hyps = " ".join(f"(h{i} : " + (f"m ≤ b{i}" if sense == "ge" else f"b{i} ≤ m") + ")" for i in range(N + 1))
        concl = f"m ≤ {nm} {bs} t" if sense == "ge" else f"{nm} {bs} t ≤ m"
        L.append(f"theorem {nm}_{sense} {{t m {bs} : ℝ}} (ht : 0 ≤ t) (ht' : t ≤ 1) {hyps} :")
        L.append(f"    {concl} := by")
        L.append("  have hs : 0 ≤ 1 - t := by linarith")
        terms = []
        for i in range(N + 1):
            d = f"(b{i} - m)" if sense == "ge" else f"(m - b{i})"
            mono = " * ".join(x for x in (_pw("t", i), _pw("(1 - t)", N - i)) if x)
            c = comb(N, i)
            if i in (0, N):
                terms.append(f"{d} * {mono}")
            else:
                terms.append(f"{c} * ({d} * ({mono}))")
        lhs = f"{nm} {bs} t - m" if sense == "ge" else f"m - {nm} {bs} t"
        L.append(f"  have e : {lhs} = " + " + ".join(terms) + f" := by unfold {nm}; ring")
        for i in range(N + 1):
            sub = f"(sub_nonneg.2 h{i})"
            pt = "ht" if i == 1 else f"(pow_nonneg ht {i})"
            ps = "hs" if N - i == 1 else f"(pow_nonneg hs {N - i})"
            if i == 0:
                fac = f"(pow_nonneg hs {N})"
            elif i == N:
                fac = f"(pow_nonneg ht {N})"
            else:
                fac = f"(mul_nonneg {pt} {ps})"
            L.append(f"  have := mul_nonneg {sub} {fac}")
        L.append("  linarith")
        L.append("")
    return "\n".join(L)


# ----------------------------------------------------------------------------------------------
# The gate library
# ----------------------------------------------------------------------------------------------


@dataclass(frozen=True)
class Gate:
    """One gate of `HybridGates`.

    key         field name in `HybridGates` (e.g. 'q_lower'); also the section title
    short       suffix of the generated Lean names (nQLower, dQLower, clearedQLower, ...)
    lean_fn     Lean gate function (e.g. 'gQLower'); applied to `fn_args`
    fn_args     parameter names (subset of B0 L0 c0 B L A D, in the Lean order) of the gate function
    mul_lemma   Lean `_mul` lemma `g * Dg = Ng` (applied to `mul_args`, then `v`, then `hyps`)
    mul_args    parameter names the `_mul` lemma takes (before `v`)
    hyps        names of the hypotheses introduced in `clearedX` and passed to the lemma; each must be
                a key of `GateLib.hyp_defs` (defaults: hx = 1 + D v ≠ 0, hE = densE ≠ 0, hF = ...)
    ne_expr     Lean term proving `Dg ≠ 0` from those hypotheses
    simp        extra `simp only` lemmas for the final `ring` step (after the n/d defs)
    cleared     Params -> (Ng, Dg): the cleared pair of the `_mul` lemma, as exact polynomials in v
    value       (Params, v) -> exact value of the gate function (independent transcription of the
                Lean definition; used to self-check `value * Dg == Ng`)
    internal    the gate is proved in the generated file but is not a field of the structure
    `lean_fn`, `mul_lemma` may contain `{floor}`, `{B0}`, ... (Lean literals of the parameters).
    """

    key: str
    short: str
    lean_fn: str
    fn_args: Tuple[str, ...]
    mul_lemma: str
    mul_args: Tuple[str, ...]
    hyps: Tuple[str, ...]
    ne_expr: str
    simp: Tuple[str, ...]
    cleared: Callable[[Params], Tuple[Poly, Poly]]
    value: Callable[[Params, Fraction], Fraction]
    internal: bool = False        # proved in the file but not a field of the structure (for gates of extension libraries)


# ---- exact transcription of the scalar definitions of HybridGates.lean (lines 31-95) ----

def _sel(P: Params, v):
    return P.A * v / (1 + P.D * v)


def _dens(P: Params, v):
    return Fr(999, 1000) * P.L0 * P.A / ((P.L0 - P.L) * (1 + P.D * v) + (6 * P.B0 - P.L0) * P.A)


def _width(P: Params, v):
    return P.s0 + v


def _packed(P: Params, v):
    return 1 - 6 * _sel(P, v)


def _rho(nu):
    return 1 - 10 * nu / (15 - 6 * nu)


def _highJ(B, L, w, u, nu):
    return 1 - _rho(nu) - nu * B + nu * (L - 1) * w - (6 * (1 - _rho(nu)) - nu - 1) * u


# ---- cleared forms, transcribed from the `g*_mul` lemmas of HybridGates.lean (lines 262-378) ----

def _cl_q_lower(P):
    return P.K - P.E / 2, P.E


def _cl_q_upper(P):
    return Fr(3, 4) * P.E - P.K, P.E


def _cl_q_floor(P):
    return P.K - P.floor * P.E, P.E


def _cl_H_lower(P):
    return P.X / 10 - 6 * P.A * V, P.X


def _cl_retained_cap(P):
    return P.c0 * (P.X - 6 * P.A * V) - P.W * P.X + P.A * V, P.X


def _cl_retained_width(P):
    return P.W * P.X - P.A * V, P.X


def _cl_low_per_width(P):
    return Poly([Fr(1, 1000) * P.L0 * P.A]), P.X


def _cl_high_at_q(P):
    Av = P.A * V
    Ng = (10 * P.K * (P.X - 6 * Av) * P.E
          - P.K * P.F * (P.B * P.X - (P.L - 1) * P.W * P.X - Av)
          + Av * P.E * P.F)
    return Ng, P.X * P.E * P.F


def _cl_high_deriv(P):
    return (Fr(25, 24) * (P.X - 6 * P.A * V)
            - (P.B * P.X - (P.L - 1) * P.W * P.X - P.A * V)), P.X


def _cl_principal(P):
    return (1 - P.B + (P.L - 2) * P.W) * P.X - Fr(9, 2) * P.A * V, P.X


def _cl_second_ref(P):
    return ((Fr(1, 20) + Fr(3, 2) * (1 - P.B) + (Fr(3, 2) * P.L - Fr(5, 2)) * P.W) * P.X
            - Fr(9, 2) * P.A * V), P.X


def _cl_second_diag(P):
    return (1 - P.B + (P.L - 1) * P.W) * P.X - 4 * P.A * V, P.X


def _cl_ref_upper(P):
    return (Fr(1, 3) - 2 * P.W) * P.X - 3 * P.A * V, P.X


def _cl_sel_deriv(P):
    return Poly([P.A]), P.X * P.X


_Q_ARGS = ("B0", "L0", "L", "A", "D")
_W_ARGS = ("B0", "L0", "B", "L", "A", "D")

#: The 14 gates of PR 83's `HybridGates`, in the order of the structure (13 gates + density floor).
GATES: Tuple[Gate, ...] = (
    Gate("q_lower", "QLower", "gQLower", _Q_ARGS, "gQLower_mul", _Q_ARGS, ("hE",), "(hE)",
         ("densE", "densK"), _cl_q_lower, lambda P, v: _dens(P, v) - Fr(1, 2)),
    Gate("q_upper", "QUpper", "gQUpper", _Q_ARGS, "gQUpper_mul", _Q_ARGS, ("hE",), "(hE)",
         ("densE", "densK"), _cl_q_upper, lambda P, v: Fr(3, 4) - _dens(P, v)),
    Gate("q_floor", "QFloor", "gQFloor", _Q_ARGS, "gQFloor_mul", _Q_ARGS, ("hE",), "(hE)",
         ("densE", "densK"), _cl_q_floor, lambda P, v: _dens(P, v) - P.floor),
    Gate("H_lower", "HLower", "gHLower", ("A", "D"), "gHLower_mul", ("A", "D"), ("hx",), "hx",
         (), _cl_H_lower, lambda P, v: _packed(P, v) - Fr(9, 10)),
    Gate("retained_cap", "RetainedCap", "gRetainedCap", ("B0", "L0", "c0", "B", "L", "A", "D"),
         "gRetainedCap_mul", ("B0", "L0", "c0", "B", "L", "A", "D"), ("hx",), "hx",
         ("width", "cross_eq"), _cl_retained_cap,
         lambda P, v: P.c0 * _packed(P, v) - (_width(P, v) - _sel(P, v))),
    Gate("retained_width", "RetainedWidth", "gRetainedWidth", _W_ARGS, "gRetainedWidth_mul",
         _W_ARGS, ("hx",), "hx", ("width", "cross_eq"), _cl_retained_width,
         lambda P, v: _width(P, v) - _sel(P, v)),
    Gate("low_per_excess_width", "LowPerWidth", "gLowPerWidth", ("L0", "A", "D"),
         "gLowPerWidth_mul", ("L0", "A", "D"), ("hx",), "hx", (), _cl_low_per_width,
         lambda P, v: Fr(1, 1000) * P.L0 * P.A / (1 + P.D * v)),
    Gate("high_at_q", "HighAtQ", "gHighAtQ", _W_ARGS, "gHighAtQ_mul", _W_ARGS,
         ("hx", "hE", "hF"), "(mul_ne_zero (mul_ne_zero hx hE) hF)",
         ("densE", "densK", "width", "cross_eq"), _cl_high_at_q,
         lambda P, v: _highJ(P.B, P.L, _width(P, v), _sel(P, v), _dens(P, v))),
    Gate("high_density_derivative", "HighDeriv", "gHighDeriv", _W_ARGS, "gHighDeriv_mul",
         _W_ARGS, ("hx",), "hx", ("width", "cross_eq"), _cl_high_deriv,
         lambda P, v: Fr(25, 24) * _packed(P, v) - (P.B - (P.L - 1) * _width(P, v) - _sel(P, v))),
    Gate("principal_reference", "Principal", "gPrincipal", _W_ARGS, "gPrincipal_mul", _W_ARGS,
         ("hx",), "hx", ("width", "cross_eq"), _cl_principal,
         lambda P, v: 1 - P.B + (P.L - 2) * _width(P, v) - Fr(9, 2) * _sel(P, v)),
    Gate("second_reference", "SecondRef", "gSecondRef", _W_ARGS, "gSecondRef_mul", _W_ARGS,
         ("hx",), "hx", ("width", "cross_eq"), _cl_second_ref,
         lambda P, v: (Fr(1, 20) + Fr(3, 2) * (1 - P.B) + (Fr(3, 2) * P.L - Fr(5, 2)) * _width(P, v)
                       - Fr(9, 2) * _sel(P, v))),
    Gate("second_diagonal", "SecondDiag", "gSecondDiag", _W_ARGS, "gSecondDiag_mul", _W_ARGS,
         ("hx",), "hx", ("width", "cross_eq"), _cl_second_diag,
         lambda P, v: 1 - P.B + (P.L - 1) * _width(P, v) - 4 * _sel(P, v)),
    Gate("reference_upper_positive", "RefUpper", "gRefUpper", _W_ARGS, "gRefUpper_mul", _W_ARGS,
         ("hx",), "hx", ("width", "cross_eq"), _cl_ref_upper,
         lambda P, v: Fr(1, 3) - 2 * _width(P, v) - 3 * _sel(P, v)),
    Gate("selection_monotonicity", "SelDeriv", "gSelDeriv", ("A", "D"), "gSelDeriv_mul",
         ("A", "D"), ("hx",), "(pow_ne_zero 2 hx)", (), _cl_sel_deriv,
         lambda P, v: P.A / (1 + P.D * v) ** 2),
)

# Lean text shared by all gates (templates: `{B0}`.. are Lean literals of the parameters, see
# `Params.lits`; literal braces must be doubled).  These are PR 86's wording.
PREAMBLE_LEMMAS: Tuple[str, ...] = (
    "theorem cross_eq : cross {B0} {L0} {B} {L} = {s0} := by\n  norm_num [cross]",
    "theorem x_pos (v : ℝ) (h0 : 0 ≤ v) : 0 < 1 + {D} * v := by nlinarith",
    "theorem E_pos (v : ℝ) (h0 : 0 ≤ v) : 0 < densE {B0} {L0} {L} {A} {D} v := by\n"
    "  unfold densE; nlinarith",
    "theorem F_pos (v : ℝ) (h0 : 0 ≤ v) :\n"
    "    0 < 15 * densE {B0} {L0} {L} {A} {D} v - 6 * densK {L0} {A} := by\n"
    "  unfold densE densK; nlinarith",
)

# `have` lines opening the proof of `clearedX`, by hypothesis name.
HYP_DEFS: Dict[str, str] = {
    "hx": "  have hx : 1 + {D} * v ≠ 0 := (x_pos v h0).ne'",
    "hE": "  have hE := (E_pos v h0).ne'",
    "hF": "  have hF := (F_pos v h0).ne'",
}

# Non-interval fields of `HybridGates` (PR 86's wording; `{mod}` = the inner namespace).
STRUCT_PREAMBLE: Tuple[str, ...] = (
    "width_pos := by rw [{mod}.cross_eq]; norm_num",
    "sel_den_pos := fun v h0 _ => {mod}.x_pos v h0",
    "dens_den_pos := fun v h0 _ => {mod}.E_pos v h0",
    "low_identity := fun v h0 _ =>\n"
    "    lowDefect_eq _ _ _ _ _ v ({mod}.x_pos v h0).ne' ({mod}.E_pos v h0).ne'",
    "low_div_eq := fun v h0 _ =>\n"
    "    lowDefect_div_eq _ _ _ _ _ v h0.ne' ({mod}.x_pos v h0.le).ne' ({mod}.E_pos v h0.le).ne'",
    "sel_hasDerivAt := fun v h0 _ => sel_hasDerivAt _ _ v ({mod}.x_pos v h0).ne'",
)


@dataclass(frozen=True)
class GateLib:
    """Everything that is specific to one version of the Lean `HybridGates` library."""

    gates: Tuple[Gate, ...] = GATES
    struct_preamble: Tuple[str, ...] = STRUCT_PREAMBLE
    preamble_lemmas: Tuple[str, ...] = PREAMBLE_LEMMAS
    hyp_defs: Tuple[Tuple[str, str], ...] = tuple(HYP_DEFS.items())
    structure: str = "HybridGates"                      # Lean structure proved by the generated theorem
    struct_args: Tuple[str, ...] = PARAM_NAMES          # its arguments (parameter names, in order)
    marked: Optional["MarkedSpec"] = None               # marked HIGH gate (3-parameter boxes), see `marked_lib`

    def replace(self, key: str, new: Gate) -> "GateLib":
        """The library with gate `key` replaced by `new` (same position)."""
        if key not in [g.key for g in self.gates]:
            raise KeyError(key)
        return replace(self, gates=tuple(new if g.key == key else g for g in self.gates))

    def without(self, key: str) -> "GateLib":
        """The library without gate `key` (the field is also dropped from the generated structure)."""
        if key not in [g.key for g in self.gates]:
            raise KeyError(key)
        return replace(self, gates=tuple(g for g in self.gates if g.key != key))

    def add(self, new: Gate, after: Optional[str] = None) -> "GateLib":
        """The library with an extra gate (appended, or after gate `after`)."""
        gs = list(self.gates)
        i = len(gs) if after is None else [g.key for g in gs].index(after) + 1
        gs.insert(i, new)
        return replace(self, gates=tuple(gs))

    def with_hyp(self, name: str, template: str) -> "GateLib":
        d = dict(self.hyp_defs)
        d[name] = template
        return replace(self, hyp_defs=tuple(d.items()))


PR83_LIB = GateLib()


def replace_gate(gates: Sequence[Gate], key: str, new: Gate) -> Tuple[Gate, ...]:
    """Return the gate tuple with the gate `key` replaced by `new`."""
    return GateLib(gates=tuple(gates)).replace(key, new).gates


# ----------------------------------------------------------------------------------------------
# Certification: boxes and Bernstein data
# ----------------------------------------------------------------------------------------------


class InfeasibleGate(Exception):
    pass


@dataclass
class Box:
    lo: Fraction
    hi: Fraction
    nb: List[Fraction]   # Bernstein coefficients of n on [lo, hi]
    db: List[Fraction]   # Bernstein coefficients of d on [lo, hi]
    m: Fraction          # min of nb   (> 0)
    M: Fraction          # max of db
    dmin: Fraction       # min of db   (> 0)
    r: Fraction          # reserve m / M


@dataclass
class GateCert:
    gate: Gate
    n: Poly
    d: Poly
    boxes: List[Box]
    r: Fraction          # gate reserve = min over boxes

    @property
    def nboxes(self) -> int:
        return len(self.boxes)


def _make_box(n: Poly, d: Poly, lo: Fraction, hi: Fraction) -> Box:
    nb, db = bernstein(n, lo, hi), bernstein(d, lo, hi)
    m, dmin, M = min(nb), min(db), max(db)
    return Box(lo, hi, nb, db, m, M, dmin, (m / M if M > 0 else Fr(0)))


def subdivide(n: Poly, d: Poly, lo: Fraction, hi: Fraction, max_depth: int = 60,
              _depth: int = 0, _gate: str = "?") -> List[Box]:
    """Bisect [lo, hi] (left to right, only the failing boxes) until every Bernstein coefficient
    of n and of d is positive on each box."""
    bx = _make_box(n, d, lo, hi)
    if bx.m > 0 and bx.dmin > 0:
        return [bx]
    # the end Bernstein coefficients are the values at lo and hi: a non-positive one cannot be cured
    if bx.nb[0] <= 0 or bx.nb[-1] <= 0 or bx.db[0] <= 0 or bx.db[-1] <= 0:
        which = lo if (bx.nb[0] <= 0 or bx.db[0] <= 0) else hi
        gv = n(which) / d(which) if d(which) != 0 else float("nan")
        raise InfeasibleGate(f"gate {_gate} is not positive: its cleared value n/d = {float(gv):.4g} <= 0 "
                             f"(or d <= 0) at v = {which} (= {float(which):.6g}) in [0, c - s0]; "
                             f"no Bernstein subdivision can prove it")
    if _depth >= max_depth:
        raise InfeasibleGate(f"gate {_gate}: still not positive after {max_depth} bisections "
                             f"around [{float(lo):.6g}, {float(hi):.6g}] (likely a zero of the numerator)")
    mid = (lo + hi) / 2
    return (subdivide(n, d, lo, mid, max_depth, _depth + 1, _gate)
            + subdivide(n, d, mid, hi, max_depth, _depth + 1, _gate))


def certify_gate(gate: Gate, P: Params, max_depth: int = 60) -> GateCert:
    Ng, Dg = gate.cleared(P)
    n, d = primitive_pair(Ng, Dg)
    boxes = subdivide(n, d, Fr(0), P.h, max_depth, _gate=gate.key)
    return GateCert(gate, n, d, boxes, min(b.r for b in boxes))


def self_check_gate(gate: Gate, P: Params, cert: GateCert, samples: int = 9) -> None:
    """Exact sanity checks of the Python model (independent of Lean):
    (1) value(v) * Dg(v) == Ng(v) at rational points of [0, h]  (the `_mul` lemma),
    (2) n/d == Ng/Dg identically (proportional polynomials),
    (3) the certified reserve is a true lower bound of the gate value at those points."""
    Ng, Dg = gate.cleared(P)
    n, d = cert.n, cert.d
    if not (Ng * d == n * Dg):
        raise AssertionError(f"{gate.key}: Ng*d != n*Dg")
    pts = [P.h * Fr(i, samples - 1) for i in range(samples)] + [P.h * Fr(3, 11), P.h * Fr(7, 13)]
    for v in pts:
        g = gate.value(P, v)
        if g * Dg(v) != Ng(v):
            raise AssertionError(f"{gate.key}: value*Dg != Ng at v={v}: the cleared form does not "
                                 f"match the gate function")
        if g < cert.r:
            raise AssertionError(f"{gate.key}: reserve {cert.r} exceeds the gate value at v={v}")


# ----------------------------------------------------------------------------------------------
# Lean file emission (PR 86 layout)
# ----------------------------------------------------------------------------------------------

FORBIDDEN = re.compile(r"\b(sorry|admit|axiom|native_decide|ofReduceBool)\b|decide\s*\+\s*native")


@dataclass
class LeanConfig:
    namespace: str = "QRH.SilDensitySplit"            # outer namespace of the generated file
    module: str = "HybridStep"                        # inner namespace; theorem is hybridGates_<module>
    gates_import: str = "Submissions.sil_density_split_20261026.Source.HybridGates"
    gates_namespace: str = "QRH.SilDensitySplit"      # namespace holding HybridGates, Hybrid.*, UnifPos
    max_heartbeats: int = 1000000
    title: Optional[str] = None                       # optional descriptor for the header comment
    theorem_name: Optional[str] = None                # default hybridGates_<module>


def _app(P: Params, fn: str, args: Sequence[str]) -> str:
    if "{" in fn:
        fn = fn.format(**P.lits())
    return " ".join([fn] + [P.lit(a) for a in args])


def _bern_ge(deg: int) -> str:
    if deg == 0:
        return "bern0_ge (by norm_num)"
    return f"{bern_fn(deg)}_ge ht ht' " + " ".join(["(by norm_num)"] * (deg + 1))


def _bern_le(deg: int) -> str:
    if deg == 0:
        return "bern0_le (by norm_num)"
    return f"{bern_fn(deg)}_le ht ht' " + " ".join(["(by norm_num)"] * (deg + 1))


def render_gate(P: Params, cert: GateCert, lib: GateLib = PR83_LIB) -> str:
    g = cert.gate
    S = g.short
    gapp = _app(P, g.lean_fn, g.fn_args)
    nname, dname = f"n{S}", f"d{S}"
    nv = "_v" if cert.n.deg == 0 else "v"
    dv = "_v" if cert.d.deg == 0 else "v"
    hyp_defs = dict(lib.hyp_defs)
    lits = P.lits()
    L: List[str] = []
    A = L.append
    A(f"/-! #### Gate `{g.key}` -/")
    A("")
    A(f"def {nname} ({nv} : ℝ) : ℝ := {lean_poly(cert.n)}")
    A("")
    A(f"def {dname} ({dv} : ℝ) : ℝ := {lean_poly(cert.d)}")
    A("")
    A(f"theorem cleared{S} (v : ℝ) (h0 : 0 ≤ v) :")
    A(f"    {gapp} v * {dname} v = {nname} v := by")
    for h in g.hyps:
        A(hyp_defs[h].format(**lits))
    margs = " ".join(P.lit(a) for a in g.mul_args)
    mlem = g.mul_lemma.format(**lits) if "{" in g.mul_lemma else g.mul_lemma
    A(f"  refine mul_eq_of_cleared {g.ne_expr} ({' '.join([mlem, margs, 'v'] + list(g.hyps))}) ?_")
    A(f"  simp only [{', '.join([nname, dname] + list(g.simp))}]")
    A("  ring")
    A("")
    nd, dd = cert.n.deg, cert.d.deg
    for k, bx in enumerate(cert.boxes):
        pt = f"({lean_real(bx.lo)} + ({lean_real(bx.hi)} - {lean_real(bx.lo)}) * t)"
        nco = " ".join(lean_real(x) for x in bx.nb)
        dco = " ".join(lean_real(x) for x in bx.db)
        A(f"theorem {nname}_bern{k} (t : ℝ) : {nname} {pt} = {bern_fn(nd)} {nco} t := by")
        A(f"  unfold {nname} {bern_fn(nd)}; ring")
        A(f"theorem {dname}_bern{k} (t : ℝ) : {dname} {pt} = {bern_fn(dd)} {dco} t := by")
        A(f"  unfold {dname} {bern_fn(dd)}; ring")
        A(f"theorem box{S}_{k} (v : ℝ) (h0 : {lean_real(bx.lo)} ≤ v) (h1 : v ≤ {lean_real(bx.hi)}) :")
        A(f"    {lean_real(bx.r)} ≤ {gapp} v := by")
        A(f"  have hb := box_lower (g := {gapp}) (n := {nname}) (d := {dname})")
        A(f"    (lo := {lean_real(bx.lo)}) (hi := {lean_real(bx.hi)}) (m := {lean_real(bx.m)}) "
          f"(M := {lean_real(bx.M)}) (by norm_num) (by norm_num)")
        A(f"    (fun v h0 _ => cleared{S} v (by linarith))")
        A("    (fun t ht ht' => by")
        A(f"      rw [{nname}_bern{k}]")
        A(f"      exact {_bern_ge(nd)})")
        A("    (fun t ht ht' => by")
        A(f"      rw [{dname}_bern{k}]")
        A(f"      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < {lean_real(bx.dmin)})")
        A(f"        ({_bern_ge(dd)}))")
        A("    (fun t ht ht' => by")
        A(f"      rw [{dname}_bern{k}]")
        A(f"      exact {_bern_le(dd)})")
        A("    v h0 h1")
        A("  exact le_trans (le_of_eq (by norm_num)) hb")
        A("")
    r = cert.r
    for k, bx in enumerate(cert.boxes):
        A(f"theorem upto{S}_{k} (v : ℝ) (h0 : {lean_real(0)} ≤ v) (h1 : v ≤ {lean_real(bx.hi)}) :")
        A(f"    {lean_real(r)} ≤ {gapp} v :=")
        if k == 0:
            A(f"  le_trans (by norm_num) (box{S}_0 v h0 h1)")
        else:
            A(f"  lower_of_two_boxes (m := {lean_real(bx.lo)}) (r₁ := {lean_real(r)}) "
              f"(r₂ := {lean_real(bx.r)})")
            A(f"    upto{S}_{k - 1} box{S}_{k} le_rfl (by norm_num) v h0 h1")
        A("")
    last = len(cert.boxes) - 1
    A(f"theorem unif{S} : UnifPos ({gapp}) 0 ({P.lit('c')} - cross {P.lit('B0')} {P.lit('L0')} "
      f"{P.lit('B')} {P.lit('L')}) := by")
    A(f"  refine ⟨{lean_real(r)}, by norm_num, fun v h0 h1 => upto{S}_{last} v h0 ?_⟩")
    A("  rw [cross_eq] at h1; linarith")
    A("")
    return "\n".join(L)


def render_header(P: Params, cfg: LeanConfig, certs: Sequence[GateCert],
                  mc: Optional["MarkedCert"] = None) -> str:
    what = cfg.title or "a density transition"
    first = (f"Exact Bernstein certificates for {what}, generated by research/density/gen_hybrid.py "
             f"(layout of PR 86's HybridK15_NN.lean, which follows Sil's Source/HybridCertificatesFirst.lean).")
    q = lambda x: "'" + plain_frac(x) + "'"
    line2 = (f"parent G({q(P.B0)}, {q(P.L0)}, {q(P.c0)}) -> child G({q(P.B)}, {q(P.L)}, {q(P.c)}), "
             f"selection A = {plain_frac(P.A)}, D = {plain_frac(P.D)}"
             + (f"; extra parameters {', '.join(f'{k} = {plain_frac(v)}' for k, v in P.extra)}" if P.extra else "")
             + ".")
    multi = " ".join(f"{c.gate.short}:{c.nboxes}" for c in certs if c.nboxes > 1)
    line3 = (f"Density floor `q >= {plain_frac(P.floor)}`; {len(certs)} gates"
             + (f"; multi-box gates ({multi})" if multi else "; one Bernstein box per gate")
             + ". Arithmetic only. -/")
    if mc is not None:
        line3 = (f"Density floor `q >= {plain_frac(P.floor)}`; {len(certs)} one-variable gates"
                 + (f" (multi-box: {multi})" if multi else " (one Bernstein box each)")
                 + f"; marked HIGH gate (repeated-mark gain, K = {MARKED_COPIES}) on the (v, nu, p) boxes "
                 f"v in [0, {plain_frac(P.h)}], nu in [q(v), 3/4] (nu = q(v) + t (3/4 - q(v)), t in [0, 1]), "
                 f"p in [0, 1/2]: "
                 + ", ".join(f"({b.branch[0]},{b.branch[1]}):{b.nleaves}" for b in mc.branches)
                 + " boxes; reserve " + plain_frac(mc.r) + ". Arithmetic only. -/")
    return f"/- {first}\n{line2}\n{line3}"


def render_file(P: Params, cfg: LeanConfig, certs: Sequence[GateCert], lib: GateLib = PR83_LIB,
                mc: Optional["MarkedCert"] = None) -> str:
    M = cfg.module
    same_ns = cfg.namespace == cfg.gates_namespace
    thm = cfg.theorem_name or (f"hybridGatesM_{M}" if mc is not None else f"hybridGates_{M}")
    lits = P.lits()
    L: List[str] = []
    A = L.append
    A(render_header(P, cfg, certs, mc))
    A(f"import {cfg.gates_import}")
    A("")
    A("set_option autoImplicit false")
    A(f"set_option maxHeartbeats {cfg.max_heartbeats}")
    A(f"namespace {cfg.namespace}")
    A("noncomputable section")
    if not same_ns:
        A(f"open {cfg.gates_namespace}")
    A(f"namespace {M}")
    A("open Hybrid")
    A("")
    for t in lib.preamble_lemmas:
        A(t.format(**lits))
        A("")
    degs = {d for c in certs for d in (c.n.deg, c.d.deg) if d > LIB_BERN_MAX}
    if mc is not None:
        degs |= {d for b in mc.branches for d in b.degn + b.degd if d > LIB_BERN_MAX}
    for d in sorted(degs):
        A(aux_bernstein_lean(d))
    for cert in certs:
        A(render_gate(P, cert, lib))
    if mc is not None:
        A(render_marked(P, cfg, mc))
    A(f"end {M}")
    A("")
    A("open Hybrid in")
    A(f"/-- Density transition G({plain_frac(P.B0)},{plain_frac(P.L0)},{plain_frac(P.c0)}) → "
      f"G({plain_frac(P.B)},{plain_frac(P.L)},{plain_frac(P.c)}), `A = {plain_frac(P.A)}`, `D = {plain_frac(P.D)}`. -/")
    A(f"theorem {thm} :")
    A(f"    {lib.structure.format(**lits)} {' '.join(P.lit(a) for a in lib.struct_args)} where")
    for f in lib.struct_preamble:
        A("  " + f.format(mod=M, **lits))
    A("")
    for cert in certs:
        if not cert.gate.internal:
            A(f"  {cert.gate.key} := {M}.unif{cert.gate.short}")
    if mc is not None:
        A(f"  high_marked := {M}.markedHigh")
    A("")
    A("end")
    A(f"end {cfg.namespace}")
    return "\n".join(L)


# ----------------------------------------------------------------------------------------------
# Marked HIGH gate: exact (v, nu, p) polynomials, tensor Bernstein boxes, Lean emission
# ----------------------------------------------------------------------------------------------
#
# The marked leaf pays the HIGH term with PR 76's repeated-mark gain `gainC` (K = 8 copies).  The
# ledger needs (field `high_marked` of `HybridGatesM`, Source/HybridGatesMarked.lean)
#
#     r <= highJ(B,L,w,u,nu) + gainC nu B0 L0 c0 (w - u) (1 - 6u)      for v in [0, c - s0], nu in [q(v), 3/4],
#
# `w = s0 + v`, `u = A v/(1 + D v)`.  `gainC` is the infimum over the amplitude classes p in [0,1/2] of the
# minimum of six facets (branches (i,j), i in {0,1} inverse, j in {0,1,2} plain), so it suffices that, for
# every branch,  G_ij(v,nu,p) = highJ + facetVal_ij >= r  for nu in [q(v), 3/4], p in [0,1/2].  The density
# is the box variable t in [0,1], nu = q(v) + t (3/4 - q(v)) = Y/E with E = densE(v), Y = K (1-t) + 3/4 t E
# (K = densK), so the region is the box [0,h] x [0,1] x [0,1/2] and no density loss is incurred.  With
# X = 1 + D v and d^ = (15-6nu)/2 U + (5-6nu) eU (U, alphaU, betaU, eU: the branch data below) one has
#
#     G_ij * (X d^) = nu (5 QX U + (5-6nu)(alphaU SX + betaU QX)) + nu ((1-2p) SX - PiX) d^ + sigX d^
#
# (`cNumM`, `cDenM`, `gHighM_ij` in the Lean library), of degree (2, 2, <= 3) in (v, nu, p); at nu = Y/E,
# multiplied by E^2, it is the polynomial pair `cNumY`, `E * cDenY` of degree (4, 2, <= 3), (3, 1, <= 2)
# in (v, t, p).  Positivity is certified by exact tensor Bernstein coefficients on boxes (subdivided in
# the variable where it helps), emitted as nested `bern2`/`bern3` forms of `Source.HybridGates`.

MARKED_COPIES = 8                                   # K: copies of each marked slot (PR 76)
MARKED_BRANCHES: Tuple[Tuple[int, int], ...] = ((0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2))
MARKED_GATES_IMPORT = "Submissions.arvi_density.Source.HybridGatesMarked"
MARKED_GATES_NAMESPACE = "QRH.ArviDensity"


@dataclass(frozen=True)
class MarkedSpec:
    """Settings of the marked HIGH gate."""
    max_boxes: int = 400         # box limit per branch
    max_depth: int = 40
    force: Tuple[int, ...] = ()  # axes (0 = v, 1 = t, 2 = p) bisected unconditionally first (tests the cover code)


class MPoly:
    """Polynomial in three variables with Fraction coefficients: dict {(a, b, c): coeff of x0^a x1^b x2^c}
    (the variables are (v, nu, p) for `marked_cleared` and (v, t, p) for `marked_scaled`)."""

    __slots__ = ("c",)

    def __init__(self, c=None):
        self.c = {k: Fr(x) for k, x in (c or {}).items() if x != 0}

    @staticmethod
    def const(a) -> "MPoly":
        return MPoly({(0, 0, 0): Fr(a)})

    @staticmethod
    def var(i: int) -> "MPoly":
        e = [0, 0, 0]
        e[i] = 1
        return MPoly({tuple(e): Fr(1)})

    @staticmethod
    def _co(x) -> "MPoly":
        return x if isinstance(x, MPoly) else MPoly.const(x)

    def __add__(self, o):
        o = MPoly._co(o)
        r = dict(self.c)
        for k, x in o.c.items():
            r[k] = r.get(k, 0) + x
        return MPoly(r)

    __radd__ = __add__

    def __neg__(self):
        return MPoly({k: -x for k, x in self.c.items()})

    def __sub__(self, o):
        return self + (-MPoly._co(o))

    def __rsub__(self, o):
        return MPoly._co(o) + (-self)

    def __mul__(self, o):
        o = MPoly._co(o)
        r: Dict[Tuple[int, int, int], Fraction] = {}
        for k1, x1 in self.c.items():
            for k2, x2 in o.c.items():
                k = (k1[0] + k2[0], k1[1] + k2[1], k1[2] + k2[2])
                r[k] = r.get(k, 0) + x1 * x2
        return MPoly(r)

    __rmul__ = __mul__

    def __pow__(self, n: int):
        r = MPoly.const(1)
        for _ in range(n):
            r = r * self
        return r

    def __eq__(self, o):
        return isinstance(o, MPoly) and self.c == o.c

    def __hash__(self):
        return hash(tuple(sorted(self.c.items())))

    def degs(self) -> Tuple[int, int, int]:
        d = [0, 0, 0]
        for k in self.c:
            for a in range(3):
                d[a] = max(d[a], k[a])
        return tuple(d)

    def __call__(self, v, nu, p) -> Fraction:
        s = Fr(0)
        pt = (Fr(v), Fr(nu), Fr(p))
        for k, x in self.c.items():
            t = x
            for a in range(3):
                t *= pt[a] ** k[a]
            s += t
        return s


_MV, _MNU, _MP = MPoly.var(0), MPoly.var(1), MPoly.var(2)


def primitive_pair3(Ng: MPoly, Dg: MPoly) -> Tuple[MPoly, MPoly]:
    """(n, d) = lambda (Ng, Dg) with integer coefficients and joint gcd 1 (lambda > 0 rational)."""
    den = 1
    for x in list(Ng.c.values()) + list(Dg.c.values()):
        den = lcm(den, x.denominator)
    ints = [int(x * den) for x in list(Ng.c.values()) + list(Dg.c.values())]
    g = reduce(gcd, ints)
    return (MPoly({k: Fr(int(x * den), g) for k, x in Ng.c.items()}),
            MPoly({k: Fr(int(x * den), g) for k, x in Dg.c.items()}))


def _power_to_bern_matrix(n: int, lo: Fraction, hi: Fraction) -> List[List[Fraction]]:
    """T with b_i = sum_j T[i][j] c_j: Bernstein coefficients (degree n) on [lo, hi] of sum c_j x^j."""
    w = hi - lo
    A = [[Fr(0)] * (n + 1) for _ in range(n + 1)]            # A[m][j]: coefficient of t^m in x^j
    for j in range(n + 1):
        for m in range(j + 1):
            A[m][j] = comb(j, m) * lo ** (j - m) * w ** m
    T = [[Fr(0)] * (n + 1) for _ in range(n + 1)]
    for i in range(n + 1):
        for m in range(i + 1):
            f = Fr(comb(i, m), comb(n, m))
            for j in range(n + 1):
                T[i][j] += f * A[m][j]
    return T


_MAT_CACHE: Dict[Tuple[int, Fraction, Fraction], List[List[Fraction]]] = {}


def bern_tensor(P: MPoly, degs: Tuple[int, int, int], lo, hi) -> Dict[Tuple[int, int, int], Fraction]:
    """Bernstein coefficient tensor of (v,nu,p) -> P on the box lo..hi (degrees `degs`): dict {(i,j,k): b}."""
    shape = [d + 1 for d in degs]
    idxs = [(i, j, k) for i in range(shape[0]) for j in range(shape[1]) for k in range(shape[2])]
    arr = {ix: P.c.get(ix, Fr(0)) for ix in idxs}
    for ax in range(3):
        key = (degs[ax], Fr(lo[ax]), Fr(hi[ax]))
        T = _MAT_CACHE.get(key)
        if T is None:
            T = _MAT_CACHE[key] = _power_to_bern_matrix(degs[ax], Fr(lo[ax]), Fr(hi[ax]))
        new = {}
        for ix in idxs:
            s = Fr(0)
            for j in range(shape[ax]):
                t = T[ix[ax]][j]
                if t:
                    s += t * arr[ix[:ax] + (j,) + ix[ax + 1:]]
            new[ix] = s
        arr = new
    return arr


def _corner_idxs(degs):
    return [(i, j, k) for i in (0, degs[0]) for j in (0, degs[1]) for k in (0, degs[2])]


@dataclass
class MBox:
    lo: Tuple[Fraction, Fraction, Fraction]
    hi: Tuple[Fraction, Fraction, Fraction]
    nb: Dict[Tuple[int, int, int], Fraction]      # Bernstein coefficients of n
    db: Dict[Tuple[int, int, int], Fraction]      # Bernstein coefficients of d
    m: Fraction                                   # min of nb (> 0)
    M: Fraction                                   # max of db
    dmin: Fraction                                # min of db (> 0)

    @property
    def r(self) -> Fraction:
        return self.m / self.M


@dataclass
class MTree:
    """Node of the box tree: a leaf (`box`) or a split of axis `axis` at `mid` into `left`, `right`."""
    lo: Tuple[Fraction, Fraction, Fraction]
    hi: Tuple[Fraction, Fraction, Fraction]
    box: Optional[MBox] = None
    axis: int = -1
    mid: Fraction = Fr(0)
    left: Optional["MTree"] = None
    right: Optional["MTree"] = None

    def leaves(self) -> List["MTree"]:
        if self.box is not None:
            return [self]
        return self.left.leaves() + self.right.leaves()


@dataclass
class MBranchCert:
    branch: Tuple[int, int]
    n: MPoly
    d: MPoly
    degn: Tuple[int, int, int]
    degd: Tuple[int, int, int]
    tree: MTree
    Ng: MPoly
    Dg: MPoly

    @property
    def nleaves(self) -> int:
        return len(self.tree.leaves())

    @property
    def r(self) -> Fraction:
        return min(lf.box.r for lf in self.tree.leaves())


@dataclass
class MarkedCert:
    branches: List[MBranchCert]
    r: Fraction                                    # the reserve written to Lean (rounded down)

    @property
    def total_boxes(self) -> int:
        return sum(b.nleaves for b in self.branches)


def marked_cleared(P: Params, i: int, j: int) -> Tuple[MPoly, MPoly]:
    """Cleared pair (Ng, Dg) of `gHighM_ij`:  G_ij * Dg = Ng  (see the Lean library `cNumM`, `cDenM`)."""
    K = MARKED_COPIES
    B0, L0, c0, B, L, A, D = P.B0, P.L0, P.c0, P.B, P.L, P.A, P.D
    s0 = P.s0
    v, nu, p = _MV, _MNU, _MP
    X = 1 + D * v
    W = s0 + v
    SX = W * X - A * v
    QX = X - 6 * A * v
    PiX = (B - (L - 1) * W) * X - A * v
    sigX = A * v
    w = 5 - 6 * nu
    x = 15 - 6 * nu
    ap, bp = 1 - p, L0 - 2 * p
    U = MPoly.const(1)
    if i == 1:
        U = U * ap
    if j == 2:
        U = U * bp
    alphaU, betaU, eU = MPoly(), MPoly(), MPoly()
    if i == 0:
        alphaU = alphaU + 2 * K * p * U
    if j == 0:
        alphaU = alphaU + p * U
    if i == 1:
        betaU = betaU + p * (bp if j == 2 else MPoly.const(1))
        eU = eU + p * (bp if j == 2 else MPoly.const(1))
    if j == 1:
        betaU = betaU + c0 * p * U
    if j == 2:
        betaU = betaU + B0 * p * (ap if i == 1 else MPoly.const(1))
        eU = eU + p * (ap if i == 1 else MPoly.const(1))
    dhat = (x * Fr(1, 2)) * U + w * eU
    nroot = 5 * QX * U + w * (alphaU * SX + betaU * QX)
    Ng = nu * nroot + nu * ((1 - 2 * p) * SX - PiX) * dhat + sigX * dhat
    return Ng, X * dhat


def marked_scaled(P: Params, i: int, j: int) -> Tuple[MPoly, MPoly]:
    """The cleared pair at `nu = Y/E`, in the variables (v, t, p): `E^2 (Ng, Dg)(v, Y/E, p)` with
    `E = densE(v)`, `Y = densK (1-t) + 3/4 t E` (Lean: `cNumY`, `E * cDenY`, `nuT_eq`).  Then
    `G_ij(v, q(v) + t (3/4 - q(v)), p) * Dg_t = Ng_t`."""
    Ng, Dg = marked_cleared(P, i, j)
    v, t = _MV, _MNU
    E = (P.L0 - P.L) * (1 + P.D * v) + (6 * P.B0 - P.L0) * P.A
    Y = P.K * (1 - t) + Fr(3, 4) * t * E

    def sub(poly: MPoly, k: int) -> MPoly:
        out = MPoly()
        for (a, b, c), x in poly.c.items():
            out = out + MPoly({(a, 0, c): x}) * (Y ** b) * (E ** (k - b))
        return out

    return sub(Ng, 2), sub(Dg, 2)


def marked_value(P: Params, i: int, j: int, v, t, p) -> Fraction:
    """Exact transcription of `gHighM = highJ + facetVal` (Gain/Gain.lean: invSlope, invOffset,
    plainSlope, plainOffset, branchSlope, branchOffset, branchRoot, facetVal) for branch (i, j) at
    `nu = q(v) + t (3/4 - q(v))`."""
    K = MARKED_COPIES
    v, t, p = Fr(v), Fr(t), Fr(p)
    q = _dens(P, v)
    nu = q + t * (Fr(3, 4) - q)
    S = _width(P, v) - _sel(P, v)
    Q = _packed(P, v)
    w = 5 - 6 * nu
    inv_slope = (Fr(1), 1 / (1 - p))[i]
    inv_off = (-(2 * p * K * S), -(p * Q) / (1 - p))[i]
    pl_slope = (Fr(1), Fr(1), 1 / (1 - 2 * p / P.L0))[j]
    pl_off = (-(2 * p * S), -(2 * p * P.c0 * Q), -(2 * p * P.B0 * Q / P.L0) / (1 - 2 * p / P.L0))[j]
    slope = 6 * nu + w * (inv_slope + pl_slope / 2)
    off = w * (inv_off + pl_off / 2)
    root = (5 * Q - off) / slope
    facet = (1 - 2 * p) * nu * S + nu * (root - Fr(10) / (15 - 6 * nu) * Q)
    return _highJ(P.B, P.L, _width(P, v), _sel(P, v), nu) + facet


def _round_down(r: Fraction, sig: int = 3) -> Fraction:
    """The largest decimal with `sig` significant digits that is <= r (r > 0)."""
    e = 0
    t = r
    while t < 1:
        t *= 10
        e += 1
    while t >= 10:
        t /= 10
        e -= 1
    s = Fr(10) ** (sig - 1 + e)
    return Fr((r * s).__floor__(), 1) / s


def subdivide3(Ng: MPoly, Dg: MPoly, n: MPoly, d: MPoly, degn, degd, lo, hi, branch, spec: MarkedSpec) -> MTree:
    """Box tree for the cleared pair: split (on the variable that raises the smallest Bernstein coefficient
    of n the most) until every Bernstein coefficient of n and d is positive."""
    count = [0]

    def make(l, h) -> MBox:
        nb, db = bern_tensor(n, degn, l, h), bern_tensor(d, degd, l, h)
        return MBox(tuple(l), tuple(h), nb, db, min(nb.values()), max(db.values()), min(db.values()))

    def split(l, h, ax, depth) -> MTree:
        mid = (l[ax] + h[ax]) / 2
        h1 = list(h)
        h1[ax] = mid
        l2 = list(l)
        l2[ax] = mid
        left = rec(l, h1, depth + 1)
        right = rec(l2, h, depth + 1)
        return MTree(tuple(l), tuple(h), axis=ax, mid=mid, left=left, right=right)

    def rec(l, h, depth) -> MTree:
        if depth < len(spec.force):
            return split(l, h, spec.force[depth], depth)
        bx = make(l, h)
        if bx.m > 0 and bx.dmin > 0:
            count[0] += 1
            if count[0] > spec.max_boxes:
                raise InfeasibleGate(f"marked gate branch {branch}: more than {spec.max_boxes} boxes")
            return MTree(tuple(l), tuple(h), box=bx)
        # a non-positive corner value cannot be cured by subdivision
        for ix in _corner_idxs(degn):
            if bx.nb[ix] <= 0:
                pt = tuple(l[a] if ix[a] == 0 else h[a] for a in range(3))
                raise InfeasibleGate(
                    f"marked gate branch {branch} is not positive: n/d = {float(n(*pt) / d(*pt)):.4g} <= 0 at "
                    f"(v, t, p) = ({', '.join(f'{float(t):.6g}' for t in pt)}), nu = q(v) + t (3/4 - q(v)); "
                    f"no subdivision can prove it")
        if depth >= spec.max_depth:
            raise InfeasibleGate(f"marked gate branch {branch}: still not positive after {depth} bisections")
        best = None
        for ax in range(3):
            mid = (l[ax] + h[ax]) / 2
            h1 = list(h)
            h1[ax] = mid
            l2 = list(l)
            l2[ax] = mid
            s = min(min(bern_tensor(n, degn, l, h1).values()), min(bern_tensor(n, degn, l2, h).values()))
            if best is None or s > best[0]:
                best = (s, ax)
        return split(l, h, best[1], depth)

    return rec(list(lo), list(hi), 0)


def certify_marked(P: Params, spec: MarkedSpec) -> MarkedCert:
    """Certify the six branches on [0,h] x [0,1] x [0,1/2] in (v, t, p) (exact), with the self-checks:
    value * Dg == Ng at rational points, Ng * d == n * Dg identically, reserve <= value."""
    lo, hi = (Fr(0), Fr(0), Fr(0)), (P.h, Fr(1), Fr(1, 2))
    out = []
    for (i, j) in MARKED_BRANCHES:
        Ng, Dg = marked_scaled(P, i, j)
        n, d = primitive_pair3(Ng, Dg)
        tree = subdivide3(Ng, Dg, n, d, n.degs(), d.degs(), lo, hi, (i, j), spec)
        out.append(MBranchCert((i, j), n, d, n.degs(), d.degs(), tree, Ng, Dg))
    r = _round_down(min(b.r for b in out))
    mc = MarkedCert(out, r)
    self_check_marked(P, mc)
    return mc


def self_check_marked(P: Params, mc: MarkedCert, samples: int = 4) -> None:
    pts = [(P.h * Fr(a, samples), Fr(b, samples), Fr(c, 2 * samples))
           for a in range(samples + 1) for b in range(samples + 1) for c in range(samples + 1)]
    for bc in mc.branches:
        i, j = bc.branch
        if not (bc.Ng * bc.d == bc.n * bc.Dg):
            raise AssertionError(f"marked branch {bc.branch}: Ng*d != n*Dg")
        for (v, t, p) in pts:
            g = marked_value(P, i, j, v, t, p)
            if g * bc.Dg(v, t, p) != bc.Ng(v, t, p):
                raise AssertionError(f"marked branch {bc.branch}: value*Dg != Ng at {(v, t, p)}: the cleared form "
                                     f"does not match the facet model")
            if g < mc.r:
                raise AssertionError(f"marked branch {bc.branch}: reserve {mc.r} exceeds the value at {(v, t, p)}")


# ---- Lean emission of the marked gate ----

def lean_mpoly(p: MPoly) -> str:
    """`(a : ℝ) + (b : ℝ) * v * ν ^ 2 + ...` (zero terms dropped)."""
    terms = []
    for (a, b, c), x in sorted(p.c.items()):
        mon = [lean_real(x)]
        if a:
            mon.append("v" if a == 1 else f"v ^ {a}")
        if b:
            mon.append("t" if b == 1 else f"t ^ {b}")
        if c:
            mon.append("p" if c == 1 else f"p ^ {c}")
        terms.append(" * ".join(mon))
    return " + ".join(terms) if terms else "(0 : ℝ)"


def _nested_bern(coef: Dict[Tuple[int, int, int], Fraction], degs) -> str:
    """Nested Bernstein form: outermost axis v (t₁), then ν (t₂), innermost p (t₃)."""
    tn = ("t₁", "t₂", "t₃")

    def level(prefix):
        ax = len(prefix)
        if ax == 3:
            return lean_real(coef[prefix])
        parts = [level(prefix + (i,)) for i in range(degs[ax] + 1)]
        return f"({bern_fn(degs[ax])} {' '.join(parts)} {tn[ax]})"

    return level(())


def _nested_proof(kind: str, degs) -> str:
    """Term proving `m ≤ nested` (kind 'ge') or `nested ≤ m` (kind 'le') from the numeric coefficient facts."""
    def level(ax):
        if ax == 3:
            return "(by norm_num)"
        parts = [level(ax + 1) for _ in range(degs[ax] + 1)]
        if degs[ax] == 0:
            return f"(bern0_{kind} {parts[0]})"
        return f"({bern_fn(degs[ax])}_{kind} ht{ax + 1} ht{ax + 1}' {' '.join(parts)})"
    return level(0)


def _bern_names(degs) -> str:
    return " ".join(sorted({bern_fn(d) for d in degs}))


def render_marked(P: Params, cfg: LeanConfig, mc: MarkedCert) -> str:
    """The Lean text of the marked HIGH gate (inside the module namespace): the helper `nuT_mem'`, per branch
    the polynomials, the cleared identity, the boxes and the cover, then `markedHigh`."""
    lits = P.lits()
    gap = lambda i, j, nu="ν": (f"gHighM {lits['B0']} {lits['L0']} {lits['c0']} {lits['B']} {lits['L']} "
                                f"{lits['A']} {lits['D']} v {nu} p ({i}, {j})")
    nuT = f"nuT {lits['B0']} {lits['L0']} {lits['L']} {lits['A']} {lits['D']} v t"
    r = mc.r
    L: List[str] = []
    A = L.append
    A("/-! #### Marked HIGH gate: `highJ + facetVal_ij ≥ r` for `ν = q(v) + t (3/4 - q(v))` -/")
    A("")
    A(f"theorem nuT_mem' (v t : ℝ) (h0 : 0 ≤ v) (hv1 : v ≤ {lits['h']}) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :")
    A(f"    1 / 2 < {nuT} ∧ {nuT} ≤ 3 / 4 := by")
    A(f"  have h1 : v ≤ {lits['c']} - cross {lits['B0']} {lits['L0']} {lits['B']} {lits['L']} := by")
    A("    rw [cross_eq]; linarith")
    A("  obtain ⟨r1, hr1, hl⟩ := unifQLower")
    A("  obtain ⟨r2, hr2, hu⟩ := unifQUpper")
    A("  have a := hl v h0 h1")
    A("  have b := hu v h0 h1")
    A("  unfold gQLower at a")
    A("  unfold gQUpper at b")
    A("  exact nuT_mem (by linarith) (by linarith) ht0 ht1")
    A("")
    hyp_args = ("(hv0 : {lo0} ≤ v) (hv1 : v ≤ {hi0}) (ht0 : {lo1} ≤ t) (ht1 : t ≤ {hi1}) "
                "(hp0 : {lo2} ≤ p) (hp1 : p ≤ {hi2})")
    # which positivity fact of `cDenY_pos_all` belongs to which branch
    dpos = {(0, 0): ".1", (0, 1): ".1", (0, 2): ".2.1", (1, 0): ".2.2.1", (1, 1): ".2.2.1", (1, 2): ".2.2.2"}
    Yexp = (f"(densK {lits['L0']} {lits['A']} * (1 - t) + 3 / 4 * t * "
            f"densE {lits['B0']} {lits['L0']} {lits['L']} {lits['A']} {lits['D']} v)")
    Eexp = f"densE {lits['B0']} {lits['L0']} {lits['L']} {lits['A']} {lits['D']} v"
    for bc in mc.branches:
        i, j = bc.branch
        ij = f"{i}{j}"
        nname, dname = f"nM{ij}", f"dM{ij}"
        A(f"/-! ##### Branch `({i}, {j})` -/")
        A("")

        def binders(poly: MPoly) -> str:     # unused variables are written `_v` (no linter warning)
            return " ".join(nm if any(k[a] for k in poly.c) else "_" + nm for a, nm in enumerate(("v", "t", "p")))
        A(f"def {nname} ({binders(bc.n)} : ℝ) : ℝ := {lean_mpoly(bc.n)}")
        A("")
        A(f"def {dname} ({binders(bc.d)} : ℝ) : ℝ := {lean_mpoly(bc.d)}")
        A("")
        A(f"theorem clearedM{ij} (v t p : ℝ) (h0 : 0 ≤ v) (hv1 : v ≤ {lits['h']}) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)")
        A(f"    (hp0 : 0 ≤ p) (hp1 : p ≤ 1 / 2) :")
        A(f"    {gap(i, j, '(' + nuT + ')')} * {dname} v t p = {nname} v t p := by")
        A(f"  have hm := nuT_mem' v t h0 hv1 ht0 ht1")
        A(f"  have hE : 0 < {Eexp} := E_pos v h0")
        A(f"  have hx : 1 + {lits['D']} * v ≠ 0 := (x_pos v h0).ne'")
        A(f"  rw [nuT_eq hE.ne'] at hm ⊢")
        A(f"  have hY : {Yexp} ≤ 3 / 4 * ({Eexp}) := by")
        A(f"    have := hm.2")
        A(f"    rw [div_le_iff₀ hE] at this")
        A(f"    exact this")
        A(f"  have P : QRH.RepeatedMarks.Params ({Yexp} / ({Eexp})) p {MARKED_COPIES} {lits['B0']} {lits['L0']} "
          f"{lits['c0']} :=")
        A(f"    ⟨by linarith [hm.1], hm.2, hp0, hp1, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,")
        A(f"      by norm_num⟩")
        A(f"  have hD := (cDenY_pos_all (x_pos v h0) hE hY hp0 hp1 (by norm_num : (1 : ℝ) < {lits['L0']})){dpos[(i, j)]}")
        A(f"  refine mul_eq_of_cleared hD.ne' (gHighM_scaled hE.ne' (gHighM_{ij} {lits['B0']} {lits['L0']} "
          f"{lits['c0']} {lits['B']} {lits['L']} {lits['A']} {lits['D']} v _ p P hx)) ?_")
        A(f"  simp only [{nname}, {dname}, cNumY, cDenY, densK, densE, width, cross_eq]")
        A("  ring")
        A("")

        def emit(tr: MTree, path: str) -> None:
            bounds = dict(lo0=lean_real(tr.lo[0]), hi0=lean_real(tr.hi[0]), lo1=lean_real(tr.lo[1]),
                          hi1=lean_real(tr.hi[1]), lo2=lean_real(tr.lo[2]), hi2=lean_real(tr.hi[2]))
            hargs = hyp_args.format(**bounds)
            if tr.box is None:
                emit(tr.left, path + "L")
                emit(tr.right, path + "R")
                A(f"theorem covM{ij}_{path} (v t p : ℝ) {hargs} :")
                A(f"    {lean_real(r)} ≤ {gap(i, j, '(' + nuT + ')')} := by")
                ax = tr.axis
                var = ("v", "t", "p")[ax]
                A(f"  rcases le_total {var} {lean_real(tr.mid)} with h | h")
                for side, child in (("left", tr.left), ("right", tr.right)):
                    cp = path + ("L" if side == "left" else "R")
                    names = ["hv0", "hv1", "ht0", "ht1", "hp0", "hp1"]
                    names[2 * ax + (1 if side == "left" else 0)] = "h"
                    A(f"  · exact {'covM' if child.box is None else 'boxM'}{ij}_{cp} v t p {' '.join(names)}")
                A("")
                return
            bx = tr.box
            pt = "({lo} + ({hi} - {lo}) * {tv})"
            args = " ".join(pt.format(lo=lean_real(tr.lo[a]), hi=lean_real(tr.hi[a]), tv=("t₁", "t₂", "t₃")[a])
                            for a in range(3))
            A(f"theorem {nname}_bern_{path} (t₁ t₂ t₃ : ℝ) :")
            A(f"    {nname} {args} =")
            A(f"      {_nested_bern(bx.nb, bc.degn)} := by")
            A(f"  unfold {nname} {_bern_names(bc.degn)}")
            A("  ring")
            A(f"theorem {dname}_bern_{path} (t₁ t₂ t₃ : ℝ) :")
            A(f"    {dname} {args} =")
            A(f"      {_nested_bern(bx.db, bc.degd)} := by")
            A(f"  unfold {dname} {_bern_names(bc.degd)}")
            A("  ring")
            A(f"theorem boxM{ij}_{path} (v t p : ℝ) {hargs} :")
            A(f"    {lean_real(r)} ≤ {gap(i, j, '(' + nuT + ')')} := by")
            A(f"  have hb := box_lower3 (g := fun v t p => {gap(i, j, '(' + nuT + ')')}) (n := {nname}) (d := {dname})")
            A(f"    (lo₁ := {bounds['lo0']}) (hi₁ := {bounds['hi0']}) (lo₂ := {bounds['lo1']}) "
              f"(hi₂ := {bounds['hi1']}) (lo₃ := {bounds['lo2']}) (hi₃ := {bounds['hi2']})")
            A(f"    (m := {lean_real(bx.m)}) (M := {lean_real(bx.M)}) (by norm_num) (by norm_num) (by norm_num) "
              f"(by norm_num)")
            A(f"    (fun v t p hv0 hv1 ht0 ht1 hp0 hp1 => clearedM{ij} v t p (by linarith) (by linarith) "
              f"(by linarith) (by linarith) (by linarith) (by linarith))")
            A("    (fun t₁ t₂ t₃ ht1 ht1' ht2 ht2' ht3 ht3' => by")
            A(f"      rw [{nname}_bern_{path}]")
            A(f"      exact {_nested_proof('ge', bc.degn)})")
            A("    (fun t₁ t₂ t₃ ht1 ht1' ht2 ht2' ht3 ht3' => by")
            A(f"      rw [{dname}_bern_{path}]")
            A(f"      exact lt_of_lt_of_le (by norm_num : (0 : ℝ) < {lean_real(bx.dmin)})")
            A(f"        ({_nested_proof('ge', bc.degd)}))")
            A("    (fun t₁ t₂ t₃ ht1 ht1' ht2 ht2' ht3 ht3' => by")
            A(f"      rw [{dname}_bern_{path}]")
            A(f"      exact {_nested_proof('le', bc.degd)})")
            A("    v t p hv0 hv1 ht0 ht1 hp0 hp1")
            A("  exact le_trans (by norm_num) hb")
            A("")

        emit(bc.tree, "r")
    # the assembly
    A("/-! #### The marked HIGH field -/")
    A("")
    A(f"theorem markedHigh : ∃ r : ℝ, 0 < r ∧ ∀ v, 0 ≤ v → v ≤ {lits['c']} - cross {lits['B0']} {lits['L0']} "
      f"{lits['B']} {lits['L']} → ∀ ν,")
    A(f"    dens {lits['B0']} {lits['L0']} {lits['L']} {lits['A']} {lits['D']} v ≤ ν → ν ≤ 3 / 4 →")
    A(f"      r ≤ highJ {lits['B']} {lits['L']} (width {lits['B0']} {lits['L0']} {lits['B']} {lits['L']} v) "
      f"(sel {lits['A']} {lits['D']} v) ν +")
    A(f"        QRH.RepeatedMarks.Source.gainC ν {lits['B0']} {lits['L0']} {lits['c0']} "
      f"(width {lits['B0']} {lits['L0']} {lits['B']} {lits['L']} v - sel {lits['A']} {lits['D']} v)")
    A(f"          (packed {lits['A']} {lits['D']} v) := by")
    A(f"  refine ⟨{lean_real(r)}, by norm_num, fun v h0 h1 ν hν1 hν2 => ?_⟩")
    A(f"  have h1' : v ≤ {lits['h']} := by rw [cross_eq] at h1; linarith")
    A("  obtain ⟨r2, hr2, hu⟩ := unifQUpper")
    A("  have hb := hu v h0 h1")
    A("  unfold gQUpper at hb")
    A(f"  have hq34 : dens {lits['B0']} {lits['L0']} {lits['L']} {lits['A']} {lits['D']} v < 3 / 4 := by linarith")
    A("  obtain ⟨t, ht0, ht1, hνt⟩ := exists_nuT hq34 hν1 hν2")
    A("  have hm := nuT_mem' v t h0 h1' ht0 ht1")
    A("  rw [← hνt] at hm")
    A("  obtain ⟨r1, hr1, hw1⟩ := unifRetainedWidth")
    A("  have hS := hw1 v h0 h1")
    A("  unfold gRetainedWidth at hS")
    A("  obtain ⟨r3, hr3, hh3⟩ := unifHLower")
    A("  have hQ := hh3 v h0 h1")
    A("  unfold gHLower at hQ")
    G = (f"highJ {lits['B']} {lits['L']} (width {lits['B0']} {lits['L0']} {lits['B']} {lits['L']} v) "
         f"(sel {lits['A']} {lits['D']} v) ν")
    A(f"  have hfac := le_gainC_of_facets (ν := ν) (B := {lits['B0']}) (lam := {lits['L0']}) (h := {lits['c0']})")
    A(f"    (S := width {lits['B0']} {lits['L0']} {lits['B']} {lits['L']} v - sel {lits['A']} {lits['D']} v) "
      f"(Q := packed {lits['A']} {lits['D']} v)")
    A(f"    (r := {lean_real(r)} - {G})")
    A("    (by linarith [hm.1]) hν2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)")
    A("    (by linarith) (by linarith)")
    A("    (fun p hp0 hp1 => forall_branch")
    for k, (i, j) in enumerate(MARKED_BRANCHES):
        bc = mc.branches[k]
        nm = f"{'covM' if bc.tree.box is None else 'boxM'}{i}{j}_r"
        end = ")" if k == len(MARKED_BRANCHES) - 1 else ""
        A(f"      (by have := {nm} v t p h0 h1' ht0 ht1 hp0 hp1; rw [← hνt] at this; unfold gHighM at this; "
          f"linarith){end}")
    A("  linarith")
    A("")
    return "\n".join(L)


def marked_lib(lib: GateLib = PR83_LIB, spec: Optional[MarkedSpec] = None) -> GateLib:
    """The gate library of `HybridGatesM qf`: PR 83's gates without the two unmarked HIGH gates
    (`high_at_q`, `high_density_derivative`), the floor `qf` as the first argument of `gQFloor`
    (this package's `HybridGates`), and the marked HIGH gate (three-parameter boxes)."""
    gs = []
    for g in lib.gates:
        if g.key in ("high_at_q", "high_density_derivative"):
            continue
        if g.key == "q_floor":
            g = replace(g, lean_fn="gQFloor {floor}", mul_lemma="gQFloor_mul {floor}")
        gs.append(g)
    return replace(lib, gates=tuple(gs), structure="HybridGatesM {floor}", marked=spec or MarkedSpec())


# ----------------------------------------------------------------------------------------------
# Driver
# ----------------------------------------------------------------------------------------------


@dataclass
class Result:
    params: Params
    config: LeanConfig
    certs: List[GateCert]
    text: str
    seconds: float
    warnings: List[str] = field(default_factory=list)
    marked: Optional["MarkedCert"] = None

    @property
    def report(self) -> str:
        P = self.params
        rows = [f"transition G({plain_frac(P.B0)}, {plain_frac(P.L0)}, {plain_frac(P.c0)}) -> "
                f"G({plain_frac(P.B)}, {plain_frac(P.L)}, {plain_frac(P.c)}), A={plain_frac(P.A)}, "
                f"D={plain_frac(P.D)}, floor={plain_frac(P.floor)}; s0={plain_frac(P.s0)}, "
                f"v in [0, {plain_frac(P.h)}]",
                f"{'gate':26s} {'deg n/d':>7s} {'boxes':>5s} {'reserve':>12s}"]
        for c in self.certs:
            rows.append(f"{c.gate.key:26s} {c.n.deg}/{c.d.deg:<5d} {c.nboxes:5d} {float(c.r):12.4e}")
        if self.marked is not None:
            mc = self.marked
            rows.append(f"marked HIGH gate (K = {MARKED_COPIES}): v in [0, {float(P.h):.6g}], t in [0, 1] "
                        f"(nu = q(v) + t (3/4 - q(v))), p in [0, 1/2]; degrees (v,t,p) of n / d, boxes, reserve")
            for b in mc.branches:
                rows.append(f"  branch ({b.branch[0]},{b.branch[1]}): {b.degn} / {b.degd} {b.nleaves:5d} boxes "
                            f"{float(b.r):12.4e}")
            rows.append(f"  global reserve written to Lean: {plain_frac(mc.r)} = {float(mc.r):.4e}")
        rows.append(f"total boxes: {sum(c.nboxes for c in self.certs)}"
                    + (f" (+ {self.marked.total_boxes} marked)" if self.marked is not None else "")
                    + f"; lines: {self.text.count(chr(10)) + 1}; generated in {self.seconds:.2f}s")
        rows += [f"warning: {w}" for w in self.warnings]
        return "\n".join(rows)

    @property
    def box_counts(self) -> Dict[str, int]:
        return {c.gate.key: c.nboxes for c in self.certs}

    def summary(self) -> dict:
        """Machine-readable report (exact rationals as strings, floats for convenience)."""
        P = self.params
        out = {
            "module": self.config.module,
            "params": {**{k: plain_frac(getattr(P, k)) for k in PARAM_NAMES}, "floor": plain_frac(P.floor),
                       **{k: plain_frac(v) for k, v in P.extra}},
            "s0": plain_frac(P.s0), "h": plain_frac(P.h),
            "total_boxes": sum(c.nboxes for c in self.certs), "lines": self.text.count("\n") + 1,
            "warnings": list(self.warnings),
            "gates": {c.gate.key: {"deg_n": c.n.deg, "deg_d": c.d.deg, "boxes": c.nboxes,
                                   "reserve": plain_frac(c.r), "reserve_float": float(c.r)}
                      for c in self.certs},
        }
        if self.marked is not None:
            mc = self.marked
            out["marked"] = {
                "reserve": plain_frac(mc.r), "reserve_float": float(mc.r),
                "total_boxes": mc.total_boxes,
                "branches": {f"{b.branch[0]}{b.branch[1]}": {
                    "deg_n": list(b.degn), "deg_d": list(b.degd), "boxes": b.nleaves,
                    "reserve": plain_frac(b.r), "reserve_float": float(b.r)} for b in mc.branches}}
        return out


def generate(P: Params, namespace: Optional[str] = None, module: Optional[str] = None,
             lib: GateLib = PR83_LIB, config: Optional[LeanConfig] = None,
             verify: bool = True, max_depth: int = 60) -> Result:
    """Certify every gate of `lib` for the transition `P` and render the Lean file.
    `config` gives the Lean-side settings; `namespace`/`module` override its fields."""
    t0 = time.time()
    cfg = config or LeanConfig()
    if namespace is not None:
        cfg = replace(cfg, namespace=namespace)
    if module is not None:
        cfg = replace(cfg, module=module)
    P.check_template_preconditions()
    for what, ident in (("namespace", cfg.namespace), ("gates namespace", cfg.gates_namespace)):
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*", ident):
            raise ValueError(f"{what} {ident!r} is not a Lean namespace")
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_']*", cfg.module):
        raise ValueError(f"module name {cfg.module!r} is not a Lean identifier")
    keys, shorts = [g.key for g in lib.gates], [g.short for g in lib.gates]
    if len(set(keys)) != len(keys) or len(set(shorts)) != len(shorts):
        raise ValueError("gate library has duplicate gate keys or duplicate Lean name suffixes")
    mc = None
    if lib.marked is not None:
        P.check_marked_preconditions()
        mc = certify_marked(P, lib.marked)
    certs = []
    for g in lib.gates:
        cert = certify_gate(g, P, max_depth)
        if verify:
            self_check_gate(g, P, cert)
        certs.append(cert)
    text = render_file(P, cfg, certs, lib, mc) + "\n"
    bad = FORBIDDEN.search(text)
    if bad:
        raise AssertionError(f"forbidden token {bad.group(0)!r} in generated Lean")
    return Result(P, cfg, certs, text, time.time() - t0, P.chain_step_warnings(), mc)


def gen_step(B0, L0, c0, B, L, c, A, D, floor=Fr(13, 20), namespace="QRH.SilDensitySplit",
             module="HybridStep", **kw) -> Result:
    """`generate` with the inputs in the order (B0, L0, c0, B, L, c, A, D, floor, namespace, module);
    values may be Fractions, ints or strings such as '99999/100000'. Further keywords go to `generate`."""
    P = Params(*[_parse_frac(x) for x in (B0, L0, c0, B, L, c, A, D)], floor=_parse_frac(floor))
    return generate(P, namespace=namespace, module=module, **kw)


# ----------------------------------------------------------------------------------------------
# Command line
# ----------------------------------------------------------------------------------------------

HEADER_RE = re.compile(
    r"parent G\(('[^']+'), ('[^']+'), ('[^']+')\) -> child G\(('[^']+'), ('[^']+'), ('[^']+')\), "
    r"selection A = ([0-9]+(?:[/.][0-9]+)?), D = ([0-9]+(?:[/.][0-9]+)?)")


def params_from_header(path: str, floor=Fr(13, 20)) -> Params:
    """Read (B0,L0,c0,B,L,c,A,D) from a `parent G(...) -> child G(...), selection A = .., D = ..` line."""
    txt = " ".join(open(path, encoding="utf-8").read().split("\n")[:8])
    m = HEADER_RE.search(txt)
    if not m:
        raise ValueError(f"{path}: no 'parent G(...) -> child G(...), selection A = .., D = ..' header")
    vals = [Fr(x.strip("'")) for x in m.groups()]
    return Params(*vals, floor=floor)


def _parse_frac(s) -> Fraction:
    """Exact rational from '99999/100000', '0.99999', '3' (numbers in JSON are read via their text)."""
    if isinstance(s, (int, float)):
        s = repr(s)
    return Fr(str(s).strip().strip("'"))


def load_gate_lib(path: str) -> GateLib:
    """Execute a Python file that defines `LIB` (a GateLib) or `modify(lib) -> GateLib`."""
    ns = runpy.run_path(path, init_globals={"gh": sys.modules["gen_hybrid"]})
    if "LIB" in ns:
        return ns["LIB"]
    if "modify" in ns:
        return ns["modify"](PR83_LIB)
    raise SystemExit(f"{path}: define LIB = GateLib(...) or modify(lib) -> GateLib")


def main(argv: Optional[Sequence[str]] = None) -> int:
    sys.modules.setdefault("gen_hybrid", sys.modules[__name__])
    ap = argparse.ArgumentParser(
        description="Generate a Lean step-certificate file for PR 83's HybridGates (PR 86 layout).",
        formatter_class=argparse.RawDescriptionHelpFormatter)
    for k in PARAM_NAMES:
        ap.add_argument(f"--{k}", type=_parse_frac, help="exact rational, e.g. 99999/100000 or 0.99999")
    ap.add_argument("--floor", type=_parse_frac, default=Fr(13, 20),
                    help="numeral of the density-floor gate q_floor (default 13/20)")
    ap.add_argument("--namespace", default="QRH.SilDensitySplit", help="outer Lean namespace of the file")
    ap.add_argument("--module", default="HybridStep",
                    help="inner namespace; the theorem is hybridGates_<module>")
    ap.add_argument("--gates-import", default=None,
                    help="Lean module defining HybridGates (default PR 83; with --marked: this package's "
                         "Source.HybridGatesMarked)")
    ap.add_argument("--gates-namespace", default=None,
                    help="Lean namespace of HybridGates/Hybrid/UnifPos in that module (default QRH.SilDensitySplit; "
                         "with --marked: QRH.ArviDensity)")
    ap.add_argument("--marked", action="store_true",
                    help="certify HybridGatesM (this package, marked HIGH leaf): PR 83's gates without the unmarked "
                         "HIGH gates, the floor as argument of gQFloor, and the marked HIGH gate on (v, nu, p) boxes")
    ap.add_argument("--marked-max-boxes", type=int, default=400, help="with --marked: box limit per branch")
    ap.add_argument("--marked-force-split", default="",
                    help="with --marked: comma-separated axes (0 = v, 1 = t, 2 = p) bisected unconditionally "
                         "before the adaptive subdivision (tests the box-cover code, e.g. 0,2)")
    ap.add_argument("--extra", action="append", default=[], metavar="NAME=VALUE",
                    help="extra scalar parameter for replaced/new gates (repeatable), e.g. --extra K=3/4")
    ap.add_argument("--max-heartbeats", type=int, default=1000000)
    ap.add_argument("--title", help="descriptor for the header comment; {i} = step number with --steps")
    ap.add_argument("--gate-lib", metavar="FILE.py",
                    help="Python file defining LIB (GateLib) or modify(lib): replaced/added/removed gates")
    ap.add_argument("--check-gates-file", metavar="HybridGates.lean",
                    help="first check the gate library against this Lean source (lean_model_check.py)")
    ap.add_argument("--from-header", metavar="FILE",
                    help="take B0..D from the 'parent G(..) -> child G(..), selection ..' header of FILE")
    ap.add_argument("--steps", metavar="JSON",
                    help="JSON list of steps {B0,L0,c0,B,L,c,A,D[,floor]}; writes one file per step")
    ap.add_argument("--outdir", help="output directory for --steps")
    ap.add_argument("--module-pattern", default="Gen_{i:02d}",
                    help="module name pattern for --steps (i = 1,2,..); also the file name")
    ap.add_argument("-o", "--output", help="output .lean file (default: stdout)")
    ap.add_argument("--dry-run", action="store_true",
                    help="certify and report only: write no Lean file (fast feasibility scan of steps)")
    ap.add_argument("--report-json", metavar="FILE",
                    help="write the per-step report (boxes, degrees, reserves) as JSON")
    ap.add_argument("--no-verify", action="store_true", help="skip the exact self-checks")
    ap.add_argument("--list-gates", action="store_true", help="print the gate table and exit")
    ap.add_argument("-q", "--quiet", action="store_true", help="no report on stderr")
    a = ap.parse_args(argv)

    lib = load_gate_lib(a.gate_lib) if a.gate_lib else PR83_LIB
    if a.marked:
        lib = marked_lib(lib, MarkedSpec(max_boxes=a.marked_max_boxes,
                                         force=tuple(int(x) for x in a.marked_force_split.split(",") if x)))
    gates_import = a.gates_import or (MARKED_GATES_IMPORT if a.marked else LeanConfig.gates_import)
    gates_namespace = a.gates_namespace or (MARKED_GATES_NAMESPACE if a.marked else LeanConfig.gates_namespace)
    extra = {k: _parse_frac(v) for k, v in (e.split("=", 1) for e in a.extra)}

    if a.list_gates:
        for g in lib.gates:
            print(f"{g.key:26s} {g.lean_fn:15s} args={' '.join(g.fn_args):22s} mul={g.mul_lemma:18s} "
                  f"hyps={','.join(g.hyps)}")
        return 0

    if a.check_gates_file and a.marked:
        print("note: --check-gates-file is not supported with --marked (the gate definitions are checked when Lean "
              "compiles the generated file); skipped", file=sys.stderr)
    elif a.check_gates_file:
        import lean_model_check as LM
        errs = LM.check_gates_file(a.check_gates_file, a.floor, lib.gates, lib.struct_preamble, extra)
        if errs:
            print(f"gate library does not match {a.check_gates_file}:", file=sys.stderr)
            for e in errs:
                print("  -", e, file=sys.stderr)
            return 2

    def cfg_for(module: str, i: Optional[int] = None) -> LeanConfig:
        title = a.title.format(i=i) if (a.title and i is not None) else a.title
        return LeanConfig(namespace=a.namespace, module=module, gates_import=gates_import,
                          gates_namespace=gates_namespace, max_heartbeats=a.max_heartbeats,
                          title=title)

    reports = []
    if a.steps:
        if not a.outdir and not a.dry_run:
            ap.error("--steps needs --outdir (or --dry-run)")
        if a.outdir:
            os.makedirs(a.outdir, exist_ok=True)
        steps = json.load(open(a.steps))
        prev, failed, nbox = None, [], 0
        for i, st in enumerate(steps, 1):
            P = Params(*[_parse_frac(st[k]) for k in PARAM_NAMES],
                       floor=_parse_frac(st["floor"]) if "floor" in st else a.floor,
                       extra={**extra, **{k: _parse_frac(v) for k, v in st.get("extra", {}).items()}})
            if prev is not None and (prev.B, prev.L, prev.c) != (P.B0, P.L0, P.c0):
                print(f"warning: step {i} parent G({plain_frac(P.B0)},{plain_frac(P.L0)},{plain_frac(P.c0)}) "
                      f"is not the child of step {i - 1}", file=sys.stderr)
            prev = P
            mod = a.module_pattern.format(i=i)
            try:
                res = generate(P, config=cfg_for(mod, i), lib=lib, verify=not a.no_verify)
            except (ValueError, InfeasibleGate) as e:
                print(f"error: step {i} ({mod}): {e}", file=sys.stderr)
                failed.append(i)
                continue
            path = os.path.join(a.outdir, f"{mod}.lean") if a.outdir and not a.dry_run else None
            if path:
                with open(path, "w", encoding="utf-8") as f:
                    f.write(res.text)
            reports.append(res.summary())
            nbox += sum(res.box_counts.values())
            if a.quiet:
                for w in res.warnings:
                    print(f"warning: step {i}: {w}", file=sys.stderr)
            if not a.quiet:
                print(f"[{i}] {path or '(dry run)'}\n{res.report}\n", file=sys.stderr)
        if a.report_json:
            json.dump(reports, open(a.report_json, "w"), indent=1)
        print(f"{len(steps) - len(failed)}/{len(steps)} steps certified"
              + ("" if a.dry_run else f", files written to {a.outdir}") + f" ({nbox} Bernstein boxes)"
              + (f"; FAILED steps: {failed}" if failed else ""), file=sys.stderr)
        return 1 if failed else 0

    if a.from_header:
        P = replace(params_from_header(a.from_header, a.floor), extra=extra)
    else:
        missing = [k for k in PARAM_NAMES if getattr(a, k) is None]
        if missing:
            ap.error("missing parameters: " + ", ".join("--" + k for k in missing)
                     + " (or use --from-header / --steps)")
        P = Params(*[getattr(a, k) for k in PARAM_NAMES], floor=a.floor, extra=extra)
    try:
        res = generate(P, config=cfg_for(a.module), lib=lib, verify=not a.no_verify)
    except (ValueError, InfeasibleGate) as e:
        print(f"error: {e}", file=sys.stderr)
        return 1
    if a.report_json:
        json.dump(res.summary(), open(a.report_json, "w"), indent=1)
    if a.output and not a.dry_run:
        with open(a.output, "w", encoding="utf-8") as f:
            f.write(res.text)
    elif not a.dry_run:
        sys.stdout.write(res.text)
    if not a.quiet or a.dry_run:
        print(res.report, file=sys.stderr)
    else:
        for w in res.warnings:
            print(f"warning: {w}", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
