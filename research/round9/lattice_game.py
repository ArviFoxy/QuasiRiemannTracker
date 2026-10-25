#!/usr/bin/env python3
"""
The unmarked zero-density exponent rho(nu) = 1 - 10 nu/(15 - 6 nu) as a lattice game.

Defender: for a bad row with saturated witnesses, count exponent of a witness of length y is
  e(y) - nu*y,  e(y) = 1 (y <= 1, diagonal moments), e(y) = (1 + 5y)/6 (y >= 1, amplified long moment);
  a plain witness of length m <= 1/2 counts 1 - 2 nu m (fourth moment).
Adversary: saturated lengths on a lattice s*N (two-term model L ~ 1 + b U^{-s(s-a)}).
Game value: max_s min(plain(s), min_k count(k s)), checked against the closed form; then
  (1) sensitivity to the long line, (2) bootstrap of the long moment from zero counts.
"""
import numpy as np

def rho(nu): return 1 - 10*nu/(15 - 6*nu)
def e(y, eps=0.0): return 1.0 if y <= 1 else (1 + 5*y)/6 - eps

def adversary_value(nu, s, eps=0.0, kmax=12):
    # all product witnesses have lengths k*s; plain witness only at s (needs s <= 1/2)
    counts = [e(k*s, eps) - nu*k*s for k in range(1, kmax+1)]
    if s <= 0.5: counts.append(1 - 2*nu*s)
    return min(counts)

def game(nu, eps=0.0):
    ss = np.linspace(0.2, 0.5, 300001)
    vals = np.array([adversary_value(nu, s, eps) for s in ss])
    k = int(np.argmax(vals))
    return vals[k], ss[k]

if __name__ == "__main__":
    print("nu     rho(closed)  game value   s*(game)  s0=5/(15-6nu)")
    for nu in [0.30, 0.40, 0.45, 0.4546, 0.50, 0.55, 0.60, 0.75]:
        v, s = game(nu)
        print(f"{nu:.4f}  {rho(nu):.6f}     {v:.6f}    {s:.5f}   {5/(15-6*nu):.5f}")
    print("\nsensitivity to the long line (intercept lowered by eps):")
    for nu in [0.45, 0.5]:
        eps = 1e-3
        v0, _ = game(nu); v1, _ = game(nu, eps)
        print(f"  nu={nu}: d(rho)/d(eps) = {(v0-v1)/eps:.4f}  (closed form 4nu/(5-2nu) = {4*nu/(5-2*nu):.4f})")
    print("\nbootstrap: long moment from zero counts, max_d' rho(d') + t d'  vs  (1+5t)/6:")
    for t in [1.155, 1.25]:
        d = np.linspace(0, 0.7494, 100001)
        f = 1 - 10*d/(15 - 6*d) + t*d
        print(f"  t={t}: bootstrap {f.max():.4f} at d'={d[f.argmax()]:.3f}  vs amplification {(1+5*t)/6:.4f}")
