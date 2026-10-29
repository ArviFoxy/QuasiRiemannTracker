#!/usr/bin/env python3
"""
Independent sympy/numpy check of the algebra behind Submissions/arvi_uniform_chain/FacetForms.lean.

Everything is transcribed from the Lean definitions of Gain/Gain.lean (invSlope, invOffset, plainSlope,
plainOffset, branchSlope, branchOffset, branchRoot, facetVal), with K = 8 and parent cap h = 1/10 unless
stated.  Notation:  w = 5 - 6 nu,  phi_k = facetVal / nu,  D(X) = (X-1)(25-18 nu) + w = (25-18 nu)(X-1+y),
y = w/(25-18 nu), so the binding-pair hypothesis  Q (B-1+y) <= S (L-1+y)  is  Q D(B) <= S D(L).

Run:  python3 facets_lean_check.py      (about 30 s; exits non-zero if any check fails)

Sections
  1  closed forms of the facets (1,0), (1,2) used by `facet10_closed`, `facet12_closed`, `facet12_half_closed`
  2  the identities stated in the task (all verified as stated; no correction was needed)
  3  identities used in the Lean proofs  (`facet10_sub_facet12`, `facet12_sub_half`, ...)
  4  exact (rational) Bernstein certificates on the box  (`poly12_nonneg`, `poly12_ratio`)
  5  numerical validation of `facets_ge_facet12`
  6  sizes of the conditions hP10, hP12 (thresholds on S/Q over the box)
"""
import itertools
import sys
from math import comb

import numpy as np
import sympy as sp
from sympy import Rational as R

FAILED = []


def check(name, cond):
    print(("OK    " if cond else "FAIL  ") + name)
    if not cond:
        FAILED.append(name)


def zero(expr):
    return sp.cancel(sp.together(expr)) == 0


# ----------------------------------------------------------------------------------------------
# Transcription of Gain/Gain.lean
# ----------------------------------------------------------------------------------------------
nu, p, B, L, S, Q, h = sp.symbols('nu p B L S Q h', real=True)
K = sp.Integer(8)
one = sp.Integer(1)
half = R(1, 2)
w = 5 - 6 * nu
base = 10 / (15 - 6 * nu)                      # baseXi nu = 10 / densityDenom nu


def invSlope(pp, i):
    return [one, 1 / (1 - pp)][i]


def invOffset(pp, i):
    return [-(2 * pp * K * S), -(pp * Q) / (1 - pp)][i]


def plainSlope(pp, j):
    return [one, one, 1 / (1 - 2 * pp / L)][j]


def plainOffset(pp, j):
    return [-(2 * pp * S), -(2 * pp * h * Q), -(2 * pp * B * Q / L) / (1 - 2 * pp / L)][j]


def branchSlope(pp, i, j):
    return 6 * nu + w * (invSlope(pp, i) + plainSlope(pp, j) / 2)


def branchOffset(pp, i, j):
    return w * (invOffset(pp, i) + plainOffset(pp, j) / 2)


def branchRoot(pp, i, j):
    return (5 * Q - branchOffset(pp, i, j)) / branchSlope(pp, i, j)


def facetVal(pp, i, j):
    return (1 - 2 * pp) * nu * S + nu * (branchRoot(pp, i, j) - base * Q)


def phi(pp, i, j):                               # facet per unit nu
    return facetVal(pp, i, j) / nu


H10 = {h: R(1, 10)}                              # parent cap used in the application
DL, DB = (L - 1) * (25 - 18 * nu) + w, (B - 1) * (25 - 18 * nu) + w
E = B * L * w - 10 * B * L - 4 * B * w - 4 * L ** 2 * w + 6 * L * w + 10 * L
a_ = 10 * L + 4 * w - L * w
bb = 3 * B * L * w + 10 * B * L - 4 * B * w + 2 * L * w - 10 * L
V = lambda pp: 12 * nu * (1 - pp) * (L - 2 * pp) + w * (2 * (L - 2 * pp) + L * (1 - pp))
M = lambda pp: 10 * (1 - pp) + w * (1 + pp)
U = 25 - 18 * nu

# ----------------------------------------------------------------------------------------------
print("== 1. closed forms")
f10 = (1 - 2 * p) * S + 2 * (5 * Q * (1 - p) + w * p * Q + w * p * S * (1 - p)) / M(p) - base * Q
check("facet10_closed:  phi10(p) = (1-2p)S + 2(5Q(1-p)+wpQ+wpS(1-p))/M(p) - 10Q/(15-6nu)",
      zero(phi(p, 1, 0) - f10))
f12 = (1 - 2 * p) * S + 2 * Q * (5 * (1 - p) * (L - 2 * p) + w * p * (L - 2 * p + B * (1 - p))) / V(p) - base * Q
check("facet12_closed:  phi12(p) = (1-2p)S + 2Q(5(1-p)(L-2p)+wp(L-2p+B(1-p)))/V(p) - 10Q/(15-6nu)",
      zero(phi(p, 1, 2) - f12))
f12h = Q * ((L - 1) * (20 - 12 * nu) + w * B) / DL - base * Q
check("facet12_half_closed:  phi12(1/2) = Q((L-1)(20-12nu)+wB)/D(L) - 10Q/(15-6nu)",
      zero(phi(half, 1, 2) - f12h))
check("V(1/2) = D(L)/2", zero(V(half) - DL / 2))
check("root10(1/2) = (2(10-6nu)Q + wS)/(25-18nu)   [BindingPair.root10_half]",
      zero(branchRoot(half, 1, 0) - (2 * (10 - 6 * nu) * Q + w * S) / U))

# ----------------------------------------------------------------------------------------------
print("== 2. identities stated in the derivation (task statement): all hold as stated")
W = sp.symbols('W')                                          # W = w, as a free symbol
sw = lambda e: sp.cancel(sp.together(e.subs(nu, (5 - W) / 6)))
N10 = lambda pp: S * ((3 * W ** 2 - 5 * W - 50) * pp + W ** 2 + 15 * W + 50) - Q * W ** 2
d10 = sw(phi(p, 1, 0) - phi(half, 1, 0)) - 2 * (1 - 2 * p) * N10(p) / ((3 * W + 10) * (W * (1 + p) + 10 * (1 - p)))
check("(1,0): phi10(p)-phi10(1/2) = 2(1-2p)N10(p)/((3w+10)(w(1+p)+10(1-p))),  N10 affine", zero(d10))
# N11 is affine in p: it is determined by the two endpoint values stated in the task
N11_0 = S * (3 * W ** 2 + 40 * W + 100) - Q * W * (R(1, 10) * W + 10 * R(1, 10) + 2 * W)
N11_half = S * (R(9, 2) * W ** 2 + 30 * W + 50) - Q * W * (2 * W + 5 * R(1, 10) - R(1, 10) * W / 2)
N11 = lambda pp: N11_0 + (N11_half - N11_0) * 2 * pp
d11 = sw((phi(p, 1, 1) - phi(half, 1, 1)).subs(H10)) - (1 - 2 * p) * N11(p) / ((3 * W + 10) * (W * (1 + p) + 10 * (1 - p)))
check("(1,1): phi11(p)-phi11(1/2) = (1-2p)N11(p)/((3w+10)(w(1+p)+10(1-p))),  N11(0), N11(1/2) as stated",
      zero(d11))
D1w = L * (3 * W + 10) - 2 * (W + 5)
D2w = -L * W * (1 + p) - 10 * L * (1 - p) + 20 * p - 4 * (5 - W) * p ** 2
d12 = sw(phi(p, 1, 2) - phi(half, 1, 2))
num12, den12 = sp.fraction(sp.factor(d12))
N12 = sp.expand(sp.cancel(num12 / (1 - 2 * p)))              # N12 with the sign convention  (1-2p) N12/(D1 D2)
check("(1,2): denominator = D1*D2 with D1 = L(3w+10)-2(w+5), D2 = -L(w(1+p)+10(1-p)) + 20p - 4(5-w)p^2",
      zero(den12 - D1w * D2w) or zero(den12 + D1w * D2w))
sgn = 1 if zero(den12 - D1w * D2w) else -1
N12 = sp.expand(sp.cancel(sgn * num12 / (1 - 2 * p)))
check("(1,2): N12 is a quadratic in p with leading coefficient 4 S (w-5) D1",
      sp.Poly(N12, p).degree() == 2 and zero(sp.Poly(N12, p).coeff_monomial(p ** 2) - 4 * S * (W - 5) * D1w))
check("(1,2): D2(1/2) = -(L-1)(1.5w+5) - w/2 and D2 is increasing in p",
      zero(D2w.subs(p, half) + (L - 1) * (R(3, 2) * W + 5) + W / 2)
      and zero(sp.diff(D2w, p) - (L * (10 - W) + 20 - 8 * (5 - W) * p)))
d00 = sw(phi(p, 0, 0) - S) - 4 * S * p * (8 * W - 5) / (W + 10)
check("(0,0): phi00 - S = 4Sp(8w-5)/(w+10)", zero(d00))
d01 = sw((phi(p, 0, 1) - S).subs(H10)) - 2 * p * (Q * W * R(1, 10) + 15 * S * W - 10 * S) / (W + 10)
check("(0,1): phi01 - S = 2p(Qw/10 + 15Sw - 10S)/(w+10)", zero(d01))
N02 = -B * Q * W * (W + 10) + 10 * Q * W - L * S * (15 * W ** 2 + 140 * W - 100) + S * p * (32 * W ** 2 + 300 * W - 200)
d02 = sw(phi(p, 0, 2) - S) - 2 * p * N02 / ((W + 10) * (20 * p - L * (W + 10)))
check("(0,2): phi02 - S = 2p N02(p)/((w+10)(20p - L(w+10))),  N02 affine", zero(d02))
gap = phi(half, 1, 0) - phi(half, 1, 2) - w * (S * DL - Q * DB) / (U * DL)
check("p=1/2:  phi10 - phi12 = w (S D(L) - Q D(B)) / ((25-18nu) D(L))   [hSsigma  <=>  S D(L) >= Q D(B)]",
      zero(gap))
check("p=1/2:  phi11 - phi10 = (w/2)(h Q - S)/slope10(1/2)   (so phi11 >= phi10 iff S <= Q/10 for h = 1/10)",
      zero(phi(half, 1, 1) - phi(half, 1, 0) - w * half * (h * Q - S) / branchSlope(half, 1, 0)))
check("D(X) = (25-18nu)(X - 1 + y(nu)),  y = w/(25-18nu)   [sigma_clear]",
      zero(DL - U * (L - 1 + w / U)) and zero(DB - U * (B - 1 + w / U)))

# ----------------------------------------------------------------------------------------------
print("== 3. identities used in the Lean proofs")
g = S * DL - Q * DB
N10n = S * ((3 * w ** 2 - 5 * w - 50) * p + w ** 2 + 15 * w + 50) - Q * w ** 2
Phi = w * g * M(p) + 2 * (1 - 2 * p) * N10n * DL
check("facet10_sub_facet12:  phi10(p) - phi12(1/2) = Phi/((25-18nu) D(L) M(p)),  Phi = w g M + 2(1-2p) N10 D(L)",
      zero(phi(p, 1, 0) - phi(half, 1, 2) - Phi / (U * DL * M(p))))
P10 = S * DL * ((15 - 12 * nu) * U) - Q * w * ((15 - 6 * nu) * DB + 2 * w * DL)
nu1 = S * (50 + 5 * w - 3 * w ** 2)
check("facet10_ge:  Phi = p w g (25-18nu) + (1-2p) P10 + S(50+5w-3w^2) D(L) (1-2p)^2",
      zero(Phi - (p * w * g * U + (1 - 2 * p) * P10 + nu1 * DL * (1 - 2 * p) ** 2)))
N10half = S * (w ** 2 + 5 * w + 10) * R(5, 2) - Q * w ** 2
check("P10 = w (w+10) g + 2 D(L) N10(1/2),  N10(1/2) = (5/2) S (w^2+5w+10) - Q w^2   [hP10_of_N10]",
      zero(P10 - (w * (w + 10) * g + 2 * DL * N10half)))
check("N10(0) - N10(1/2) = S(50+5w-3w^2)/2 >= 0  (so N10(1/2) >= 0 implies N10(0) >= 0)",
      zero(N10n.subs(p, 0) - N10n.subs(p, half) - nu1 / 2))
check("facet10_le_facet11:  phi11 - phi10 = w p (h Q - S)/slope10(p)",
      zero(phi(p, 1, 1) - phi(p, 1, 0) - w * p * (h * Q - S) / branchSlope(p, 1, 0)))
F0 = (DL ** 2 * S + w * Q * E) / 4
F1 = -(a_ * DL * S - w * bb * Q) / 2
F2 = 12 * nu * S * DL
Ftay = F0 + F1 * (p - half) + F2 * (p - half) ** 2
check("facet12_sub_half:  phi12(p) - phi12(1/2) = 2 (1-2p) [F0 + F1 (p-1/2) + F2 (p-1/2)^2] / (D(L) V(p))",
      zero(phi(p, 1, 2) - phi(half, 1, 2) - 2 * (1 - 2 * p) * Ftay / (DL * V(p))))
Fw = lambda e: e.subs(nu, (5 - W) / 6)
check("F = -N12/2  (N12 of the task):  F0 = -N12(1/2)/2,  F1 = -N12'(1/2)/2,  F2 = -lead(N12)/2",
      zero(Fw(F0) + N12.subs(p, half) / 2)
      and zero(Fw(F1) + sp.diff(N12, p).subs(p, half) / 2)
      and zero(Fw(F2) + 4 * S * (W - 5) * D1w / 2))
poly = -a_ * E - bb * DL
check("facet12_ge:  D(L) (a D S - w bb Q) = a (S D^2 + w Q E) + w Q (-a E - bb D)",
      zero(DL * (a_ * DL * S - w * bb * Q) - (a_ * (S * DL ** 2 + w * Q * E) + w * Q * poly)))
# eight-copy facets: phi0j - phi1j = (w p/(1-p)) g_j / ((A+w)(A + w/(1-p)))   with A = 6nu + w t/2
t_, q_ = sp.symbols('t q', real=True)
Aw = 6 * nu + w * t_ / 2
r1 = (5 * Q - w * (-(p * Q) / (1 - p) + q_ / 2)) / (Aw + w / (1 - p))
r0 = (5 * Q - w * (-(2 * p * K * S) + q_ / 2)) / (Aw + w)
gj = 2 * K * S * (Aw * (1 - p) + w) - w / 2 * (q_ + Q * t_)
check("root_cmp_aux:  root0 - root1 = (w p/(1-p)) g / ((A+w)(A+w/(1-p))),  g = 2KS(A(1-p)+w) - (w/2)(q+Qt)",
      zero(r0 - r1 - w * p / (1 - p) * gj / ((Aw + w) * (Aw + w / (1 - p)))))
for j in range(3):
    sub = {t_: plainSlope(p, j), q_: plainOffset(p, j)}
    Aj_, gjj = Aw.subs(sub), gj.subs(sub)
    check("branch (0,%d) vs (1,%d): root0 - root1 = (w p/(1-p)) g_%d / ((A+w)(A+w/(1-p)))" % (j, j, j),
          zero(branchRoot(p, 0, j) - branchRoot(p, 1, j)
               - w * p / (1 - p) * gjj / ((Aj_ + w) * (Aj_ + w / (1 - p)))))

# ----------------------------------------------------------------------------------------------
print("== 4. exact Bernstein certificates on the box  w in [1/2,2], L in [19/10,13/5], B in [22/23,1]")
wv, Bv, Lv = sp.symbols('wv Bv Lv', real=True)
s_, t2_, b_ = sp.symbols('s t2 b', real=True)


def bernstein_min(poly_expr, degs):
    sub = {wv: R(1, 2) + R(3, 2) * s_, Lv: R(19, 10) + R(7, 10) * t2_, Bv: R(22, 23) + b_ / 23}
    P = sp.Poly(sp.expand(poly_expr.subs(sub)), s_, t2_, b_)
    terms = dict(P.terms())
    best = None
    for idx in itertools.product(*[range(d + 1) for d in degs]):
        tot = 0
        for mon, c in terms.items():
            if all(mon[k] <= idx[k] for k in range(3)):
                f = 1
                for k in range(3):
                    f *= R(comb(idx[k], mon[k]), comb(degs[k], mon[k]))
                tot += c * f
        best = tot if best is None else min(best, tot)
    return best


Dw = Lv * (3 * wv + 10) - 2 * (wv + 5)
Ew = Bv * Lv * wv - 10 * Bv * Lv - 4 * Bv * wv - 4 * Lv ** 2 * wv + 6 * Lv * wv + 10 * Lv
aw = 10 * Lv + 4 * wv - Lv * wv
bw = 3 * Bv * Lv * wv + 10 * Bv * Lv - 4 * Bv * wv + 2 * Lv * wv - 10 * Lv
m1 = bernstein_min(-aw * Ew - bw * Dw, (2, 3, 1))
check("poly12_nonneg: -a E - bb D >= 0 on the box; min Bernstein coefficient (degrees 2,3,1) = %s ~ %.4f"
      % (m1, float(m1)), m1 > 0)
m2 = bernstein_min(Dw ** 2 / 13 + wv * Ew, (2, 2, 1))
check("poly12_ratio: D^2/13 + w E >= 0 on the box; min Bernstein coefficient (degrees 2,2,1) = %s ~ %.4f"
      % (m2, float(m2)), m2 > 0)
tau_corner = float((-(wv * Ew) / Dw ** 2).subs({wv: 2, Bv: 1, Lv: R(19, 10)}))
print("   (largest S/Q needed by hP12 on the box is at the corner w=2, B=1, L=19/10: %.5f < 1/13 = %.5f)"
      % (tau_corner, 1 / 13))

# ----------------------------------------------------------------------------------------------
print("== 5. numerical validation of facets_ge_facet12 (K = 8, h = 1/10)")
rng = np.random.default_rng(20261029)
N = 400000
nuv = rng.uniform(0.5, 0.75, N)
Bn = rng.uniform(22 / 23, 1, N)
Ln = rng.uniform(1.9, 2.6, N)
# S/Q = r in [1/50 .. 1/10]  (S in [1/50,1/10], Q in [9/10,1] and S <= Q/10)
Qn = rng.uniform(0.9, 1, N)
Sn = rng.uniform(0.02, 0.1, N)
wn = 5 - 6 * nuv
Dl = (Ln - 1) * (25 - 18 * nuv) + wn
Db = (Bn - 1) * (25 - 18 * nuv) + wn
hSQ = Sn <= Qn / 10
hSs = Qn * Db <= Sn * Dl
hP10 = Qn * wn * ((15 - 6 * nuv) * Db + 2 * wn * Dl) <= Sn * Dl * ((15 - 12 * nuv) * (25 - 18 * nuv))
En = Bn * Ln * wn - 10 * Bn * Ln - 4 * Bn * wn - 4 * Ln ** 2 * wn + 6 * Ln * wn + 10 * Ln
hP12 = Sn * Dl ** 2 + wn * Qn * En >= 0
print("   sampled box points: %d;  hSQ&hSsigma: %.3f;  +hP10: %.3f;  +hP12 (all hypotheses): %.3f"
      % (N, (hSQ & hSs).mean(), (hSQ & hSs & hP10).mean(), (hSQ & hSs & hP10 & hP12).mean()))


def facet(i, j, pp):
    invS = [np.ones_like(pp), 1 / (1 - pp)][i]
    invO = [-(2 * pp * 8 * Sn), -(pp * Qn) / (1 - pp)][i]
    plS = [np.ones_like(pp), np.ones_like(pp), 1 / (1 - 2 * pp / Ln)][j]
    plO = [-(2 * pp * Sn), -(2 * pp * 0.1 * Qn), -(2 * pp * Bn * Qn / Ln) / (1 - 2 * pp / Ln)][j]
    slope = 6 * nuv + wn * (invS + plS / 2)
    off = wn * (invO + plO / 2)
    root = (5 * Qn - off) / slope
    return (1 - 2 * pp) * nuv * Sn + nuv * (root - 10 / (15 - 6 * nuv) * Qn)


ones = np.ones(N)
target = facet(1, 2, 0.5 * ones)
ps = np.concatenate([np.linspace(0, 0.5, 101), [0.4999, 0.499, 0.495, 0.49]])
slack = {}
for i in range(2):
    for j in range(3):
        m = np.full(N, np.inf)
        for pp in ps:
            m = np.minimum(m, facet(i, j, pp * ones) - target)
        slack[(i, j)] = m
mn_all = min(slack[k][hSQ & hSs & hP10 & hP12].min() for k in slack)
check("conclusion holds for every sampled point satisfying all hypotheses (min slack %.3e, all facets, 105 values of p)"
      % mn_all, mn_all > -1e-12)
# hP12 is necessary: if S D^2 + w Q E < 0 the facet (1,2) is increasing at p = 1/2, so the conclusion fails
# for p slightly below 1/2.  F0 = (S D^2 + w Q E)/4, F1 = -(a D S - w bb Q)/2 are the Taylor coefficients;
# the violation lives on (1/2 - |F0|/|F1|, 1/2), so the probe point is p = 1/2 - |F0|/(4|F1|).
an = 10 * Ln + 4 * wn - Ln * wn
bn = 3 * Bn * Ln * wn + 10 * Bn * Ln - 4 * Bn * wn + 2 * Ln * wn - 10 * Ln
F0n = (Dl ** 2 * Sn + wn * Qn * En) / 4
F1n = -(an * Dl * Sn - wn * bn * Qn) / 2
viol12 = hSQ & hSs & (F0n < -1e-6)
probe = 0.5 - np.minimum(0.01, np.abs(F0n) / (4 * np.abs(F1n) + 1e-12))
neg = facet(1, 2, probe) - target
check("hP12 is necessary: all %d sampled points with hSQ, hSsigma, S D^2 + wQE < -4e-6 violate the conclusion "
      "for k=(1,2) (probe p just below 1/2)" % viol12.sum(), (neg[viol12] < 0).all())
rat = (Qn <= 13 * Sn) & hSQ & hSs
check("facets_ge_facet12_of_ratio: Q <= 13 S (with hSQ, hSsigma) implies hP10 and hP12 and the conclusion on all samples",
      (hP10[rat]).all() and (hP12[rat]).all()
      and min(slack[k][rat].min() for k in slack) > -1e-12)
print("   (fraction of sampled points with hSQ, hSsigma and Q <= 13 S: %.3f)" % rat.mean())
# margins of the eight-copy domination g_j on the box (corner + random)
for j, nm in enumerate(["(0,0)", "(0,1)", "(0,2)"]):
    pp = rng.uniform(0, 0.5, N)
    t = [np.ones(N), np.ones(N), 1 / (1 - 2 * pp / Ln)][j]
    q = [-(2 * pp * Sn), -(2 * pp * 0.1 * Qn), -(2 * pp * Bn * Qn / Ln) / (1 - 2 * pp / Ln)][j]
    A = 6 * nuv + wn * t / 2
    gjn = 16 * Sn * (A * (1 - pp) + wn) - wn / 2 * (q + Qn * t)
    check("branch %s: g_j >= 0 on the box, min g_j over %d samples = %.3f" % (nm, N, gjn.min()), gjn.min() > 0)

# ----------------------------------------------------------------------------------------------
print("== 6. sizes of the conditions (thresholds on S/Q, Q = 1) over the box")
g_nu, g_B, g_L = np.meshgrid(np.linspace(0.5, 0.75, 101), np.linspace(22 / 23, 1, 41), np.linspace(1.9, 2.6, 71),
                             indexing='ij')
gw = 5 - 6 * g_nu
gU = 25 - 18 * g_nu
gDL = (g_L - 1) * gU + gw
gDB = (g_B - 1) * gU + gw
sig = gDB / gDL                                                    # hSsigma:  S/Q >= sigma
gE = g_B * g_L * gw - 10 * g_B * g_L - 4 * g_B * gw - 4 * g_L ** 2 * gw + 6 * g_L * gw + 10 * g_L
tau12 = -gw * gE / gDL ** 2                                        # hP12:     S/Q >= tau12
tau10 = gw * ((15 - 6 * g_nu) * gDB + 2 * gw * gDL) / (gDL * (15 - 12 * g_nu) * gU)   # hP10: S/Q >= tau10
tau10s = 2 * gw ** 2 / (5 * (gw ** 2 + 5 * gw + 10))               # N10(1/2) >= 0: S/Q >= tau10s
print("   max sigma = %.4f (> 1/10 only where hSQ & hSsigma are incompatible),  max tau12 = %.4f (< 1/13),"
      "  max tau10s = %.4f (= 1/15 at nu = 1/2)" % (sig.max(), tau12.max(), tau10s.max()))
print("   max (tau10 - max(sigma, tau12)) = %.2e  (hP10 is implied by hSsigma & hP12 up to this, near nu = 3/4)"
      % (tau10 - np.maximum(sig, tau12)).max())
print("   max (tau10 - max(sigma, tau12, 1/50)) = %.2e  (<= 0: with S/Q >= 1/50 from the box, hP10 follows "
      "numerically from hSsigma & hP12; not formalised)" % (tau10 - np.maximum.reduce([sig, tau12, 0.02 + 0 * sig])).max())
print("   max (tau10 - tau10s) = %.2e,  so hP10 is weaker than N10(1/2) >= 0 (given hSsigma)" % (tau10 - tau10s - 0).max()
      if False else "   (hP10 is weaker than N10(1/2) >= 0 given hSsigma: Lean lemma hP10_of_N10)")


def phi10n(nu_, pp, S_, Q_=1.0):
    w_ = 5 - 6 * nu_
    slope = 6 * nu_ + w_ * (1 / (1 - pp) + 0.5)
    off = w_ * (-(pp * Q_) / (1 - pp) - pp * S_)
    return (1 - 2 * pp) * S_ + (5 * Q_ - off) / slope - 10 / (15 - 6 * nu_) * Q_


def exact_threshold_10(nu_, B_, L_):
    w_ = 5 - 6 * nu_
    x_ = w_ / (2 * (5 + w_))
    T_ = (L_ - 1 + x_ * B_) / (L_ - 1 + x_ * L_) - 10 / (10 + w_)
    pgrid = np.linspace(0, 0.5, 801)
    lo, hi = 0.0, 0.3
    for _ in range(45):
        mid = (lo + hi) / 2
        if min(phi10n(nu_, pp, mid) for pp in pgrid) - T_ >= 0:
            hi = mid
        else:
            lo = mid
    return hi


print("   worst corner nu = 1/2, B = 22/23, L = 13/5:  sigma = %.4f,  tau12 = %.4f,  tau10 = %.4f,  tau10s = %.4f, "
      " exact threshold for facet (1,0) = %.4f"
      % (sig[0, 0, -1], tau12[0, 0, -1], tau10[0, 0, -1], tau10s[0, 0, -1], exact_threshold_10(0.5, 22 / 23, 2.6)))

print()
if FAILED:
    print("FAILED:", FAILED)
    sys.exit(1)
print("all checks passed")
