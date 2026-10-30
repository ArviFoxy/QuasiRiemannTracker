"""Theta span V of the sextic large sieve: where does the excess live, and what is left off it?

Matrix E[z, x] = chi_z(x) = prod_{pi | z} (x/pi)_6: rows z = squarefree ideals with N(z) in [B, 2B] coprime to 6 (the
moduli), columns x = primary elements with squarefree norm <= L (the sources).  Xu-Sang (arXiv 2610.17675) attain the
de Faveri excess with Gauss-sum vectors on the moduli side, c_z = conj G(z,1) * profile(N z / B): their Gram main term
is a rank-one form in the profile, proportional to I(U) = int U(t) t^{-5/6} dt.  This script measures, at the sizes we
can reach:
  * the dual energy ratio r(c) = ||E^T c||^2 / (S ||c||^2) of theta row vectors (random c gives 1; the Marchenko-
    Pastur edge is (sqrt R + sqrt S)^2 / S), with Gauss-sum conjugation/unit-twist variants;
  * the Gram of theta vectors across radial profiles (rank-one test against I(U));
  * the overlap of the theta direction with the top singular vectors of E;
  * the projections of detectors (plain sum, prime pool, random) onto the source-side theta direction E^T c / |.|;
  * the top singular value of E with the theta direction removed ("large sieve off V").
G(z,1) uses the Kubota character e(Tr(x/(sqrt(-3) z))) (ppcore 'canon'), extended to composite z by
G(c1 c2) = (c1/c2)_6 (c2/c1)_6 G(c1) G(c2).

usage: python3 -I theta_profile.py B L
"""
import os, sys, math, time
sys.dont_write_bytecode = True
import numpy as np

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_core as tc      # noqa: E402

B = int(sys.argv[1]); L = int(sys.argv[2])
rng = np.random.default_rng(5)
F = tc.build(B, L)
E, R, S, rows, SA, SB, SN, spf, ID = F.E, F.R, F.S, F.rows, F.SA, F.SB, F.SN, F.spf, F.ID
Grow, unit_tw, generator, sym, sqfree_int, pc, t0 = F.Grow, F.unit_tw, F.generator, F.sym, F.sqfree_int, F.pc, F.t0


# ---------------------------------------------------------------- profile test: is the theta excess rank one in the profile?
def ratio(c):
    v = E.T @ c
    return float(np.vdot(v, v).real / (S * np.vdot(c, c).real))
tN = rows['N'] / B
base = np.conj(Grow) * unit_tw[:, 0]
tt = np.linspace(1, 2, 4001)
def Ival(f):
    return np.trapezoid(f(tt) * tt ** (-5 / 6), tt)
# profile family on [1,2] (as functions of t = N/B); weights t^{-1/2} as in Xu-Sang
p_main = lambda t: t ** (-5 / 6)                      # the I-representer direction
p_lin = lambda t: (t - 1.5)                           # adjust to I = 0 below
alpha = Ival(p_lin) / Ival(lambda t: np.ones_like(t))
p_zero = lambda t: (t - 1.5) - alpha                  # I(p_zero) = 0
p_osc = lambda t: np.cos(2 * np.pi * (t - 1))
beta = Ival(p_osc) / Ival(lambda t: np.ones_like(t))
p_osc0 = lambda t: np.cos(2 * np.pi * (t - 1)) - beta # I = 0
print('I(p_zero) = %.2e, I(p_osc0) = %.2e' % (Ival(p_zero), Ival(p_osc0)))
for name, pf in (('t^-5/6 (I-direction)', p_main), ('flat', lambda t: np.ones_like(t)),
                 ('linear, I=0', p_zero), ('cosine, I=0', p_osc0)):
    w = pf(tN) * tN ** -0.5
    rt = ratio(base * w)
    rr = [ratio(np.exp(2j * np.pi * rng.random(R)) * w) for _ in range(20)]
    print('  profile %-22s theta r = %.3f   random-phase r = %.3f +- %.3f   excess %+.1f%% (%.1f sd)' %
          (name, rt, np.mean(rr), np.std(rr), 100 * (rt / np.mean(rr) - 1), (rt - np.mean(rr)) / np.std(rr)))
