#!/usr/bin/env python3
"""
Reconstruct the three-line count (I, P, L) at the binding bin and its sensitivities,
then tabulate what each large-values method can give.

Lines (count exponents log_U #bad rows), as in the brief:
  I(r) = 1 - d (p + (1-p) r)                 marked inverse, r <= 1  (z=(1-r)/2)
  P(m) = 1 - 2 d m - 2 d p (B - 2m)/Lam      plain 4th moment with slots
  L(t) = 1/6 + (5/6 - d) t                   sixth-power amplified long moment, t >= 1
Detector at t in [1, 3/2]: each bad row has (r, m), r + m >= t, r <= t, m <= 1/2.
Count(t) = max( L(t), max_{t-1/2 <= r < 1} min(I(r), P(t-r)) ),   R = min_t Count(t).
"""
import numpy as np
from scipy.optimize import brentq, minimize_scalar

def lines(d, p, B, Lam, sI=0.0, sP=0.0, sL=0.0):
    I = lambda r: 1 - d*(p + (1-p)*r) - sI
    P = lambda m: 1 - 2*d*m - 2*d*p*(B - 2*m)/Lam - sP
    L = lambda t: 1/6 + (5/6 - d)*t - sL
    return I, P, L

def count_t(t, d, p, B, Lam, **kw):
    I, P, L = lines(d, p, B, Lam, **kw)
    rs = np.linspace(max(t-0.5, 0.0), min(1.0, t), 4001)
    short = np.max(np.minimum(I(rs), P(t-rs)))
    return max(L(t), short), short

def corner(d, p, B, Lam, **kw):
    f = lambda t: count_t(t, d, p, B, Lam, **kw)[0]
    res = minimize_scalar(f, bounds=(1.0, 1.5), method='bounded', options={'xatol':1e-10})
    t = res.x
    I, P, L = lines(d, p, B, Lam, **kw)
    rs = np.linspace(max(t-0.5, 0.0), min(1.0, t), 200001)
    v = np.minimum(I(rs), P(t-rs)); k = np.argmax(v)
    return res.fun, t, rs[k], t-rs[k]

if __name__ == "__main__":
    d, p, Lam = 0.4546, 0.5, 2.6
    # calibrate B so that R = 0.6037 (brief's value); the brief quotes B ~ 0.94
    B = brentq(lambda B: corner(d, p, B, Lam)[0] - 0.6037, 0.90, 1.0)
    R, t, r, m = corner(d, p, B, Lam)
    print(f"calibrated face B={B:.5f}, Lam={Lam}:  R={R:.6f} t*={t:.4f} r*={r:.4f} m*={m:.4f}")
    R94 = corner(d, p, 0.94, Lam)
    print(f"with B=0.94 exactly: R={R94[0]:.6f} t*={R94[1]:.4f} r*={R94[2]:.4f} m*={R94[3]:.4f}")
    eps = 1e-4
    for name in ['sI', 'sP', 'sL']:
        R2 = corner(d, p, B, Lam, **{name: eps})[0]
        print(f"  dR/d(lower {name[1]} line) = {(R-R2)/eps:.4f}  -> line drop needed for -7.5e-5: {7.5e-5/((R-R2)/eps):.2e}")
    # all short lines (I and P) lowered together
    R2 = corner(d, p, B, Lam, sI=eps, sP=eps)[0]
    print(f"  dR/d(lower I and P together) = {(R-R2)/eps:.4f}")

    # unmarked rho(nu)
    for nu in [0.45, 0.4546, 0.48, 0.5, 0.51]:
        Ru, tu, ru, mu = corner(nu, 0.0, 1.0, 1.0)   # p=0 kills slot term
        rho = 1 - 10*nu/(15 - 6*nu)
        sens = {}
        for name in ['sI', 'sP', 'sL']:
            sens[name] = (Ru - corner(nu, 0.0, 1.0, 1.0, **{name: eps})[0])/eps
        print(f"nu={nu}: rho={rho:.6f} (LP {Ru:.6f}) t={tu:.4f} r={ru:.4f} m={mu:.4f}  "
              f"sens I {sens['sI']:.3f} P {sens['sP']:.3f} L {sens['sL']:.3f}")

    print("\n=== method table at the corner ===")
    dd = d
    lenI = (1 + r)/2          # marked inverse witness M_r * Q, z=(1-r)/2, total length
    lenP = 2*m + (B - 2*m)/Lam  # S_m^2 * Q
    print(f"witness lengths: inverse(marked) y={lenI:.4f}, Moebius alone y={r:.4f}, plain S^2Q y={lenP:.4f}, S alone {m:.4f}, long t={t:.4f}")
    # density-hypothesis (coefficient-blind) barrier y(1-delta)
    for nm, y in [('I marked', lenI), ('Moeb alone', r), ('P (S^2Q)', lenP), ('long', t)]:
        print(f"  coefficient-blind floor y(1-d) for {nm}: {y*(1-dd):.4f}")
    print(f"  long line L(t*)={1/6+(5/6-dd)*t:.4f}  vs blind floor t*(1-d)={t*(1-dd):.4f}  (L below floor iff t>1)")
    # Halasz with off-diagonal negligible only beyond conductor U^2
    print(f"Halasz best (length past conductor U^2): 2(1-d) = {2*(1-dd):.4f}")
    # Jutila/HB-type: R <= U Y^{k(1-2d)} >= U
    print(f"Jutila/HB: exponent 1 + k*y*(1-2d) >= 1 for all k,y  (1-2d={1-2*dd:.4f})")
    # GM cubic trace, E2 via 4th moment of coset family, S3 assumed <= S2 (H2)
    for lab, a in [('proved width-2 4th moment', 2/3), ('ideal width-1 4th moment (H1)', 1/3)]:
        f = lambda y: y*(4 - 6*dd)/3 + a
        print(f"GM+(H2) with {lab}: rho(y)= y*{(4-6*dd)/3:.4f} + {a:.4f}; at I-witness {f(lenI):.4f}, "
              f"Moeb {f(r):.4f}, S^2Q {f(lenP):.4f}; fixed point y=rho: {a/(1-(4-6*dd)/3):.4f}")
    # same at nu=0.5
    nu = 0.5
    for lab, a in [('proved', 2/3), ('ideal (H1)', 1/3)]:
        print(f"nu=0.5 GM+(H2) {lab}: rho(y) = y*{(4-6*nu)/3:.4f}+{a:.4f}; fixed point {a/(1-(4-6*nu)/3):.4f}")
