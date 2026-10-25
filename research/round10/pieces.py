#!/usr/bin/env python3
"""
Round 10: count exponents for the pieces of the long Mobius witness M(D), D = U^t, on bin rows,
under mu*log = -Lambda*mu (M(D) log D = -sum_P Q(P) M(D/P)).
  pointwise prime block on bin rows (Lemma 19.1 amplitude cap): |Q(P)|^2 <= P^{1+delta}
  Mobius block of length D/P: MI diagonal if D/P <= U, amplified (1+5y)/6 otherwise.
Count exponent of a piece = log_U( mean-value bound / D^{1+delta} ).  Compare with the
amplified long line L(t) = (1+5t)/6 - delta t.
Also the global-strip variant (all rows zero-free right of beta*, pointwise exponent delta* = 2beta*-1).
"""
import numpy as np

def piece(p, t, d_pt, delta):
    """prime part length U^p bounded pointwise with exponent d_pt (|Q|^2 <= P^{1+d_pt}),
    Mobius part length U^(t-p) by mean value."""
    y = t - p
    mv = 1 + y if y <= 1 else (1 + 5*y)/6 + y       # unnormalized: (rows-normalized mean) * length
    return p*(1 + d_pt) + mv - t*(1 + delta)

def L(t, delta):
    return (1 + 5*t)/6 - delta*t

for (t, delta) in [(1.155, 0.4546), (1.2195, 0.45), (1.25, 0.5)]:
    print(f"t = {t}, delta = {delta}: amplified long line L(t) = {L(t, delta):.4f}")
    for p in [0.0, 0.05, 0.1, t - 1, 0.2, 0.25, 0.3, 0.35, 0.4, 0.5, 0.75, 1.0, t]:
        print(f"   prime length p = {p:.3f}: bin cap {piece(p, t, delta, delta):.4f}"
              f"   global strip (delta* = 0.749) {piece(p, t, 0.749, delta):.4f}")
    ps = np.linspace(0, t, 100001)
    good = ps[[piece(p, t, delta, delta) < L(t, delta) for p in ps]]
    print(f"   pieces beating L(t) with the bin cap: p in ({good.min():.4f}, {good.max():.4f})")
    s0 = 5/(15 - 6*delta)
    print(f"   lattice adversary scale s0 = {s0:.4f}: its pieces sit at p = s0, 2s0, 3s0 ->"
          f" {[round(piece(k*s0, 3*s0, delta, delta), 4) for k in (1, 2, 3)]} at t = 3s0"
          f" (rho = {1 - 10*delta/(15 - 6*delta):.4f})")
