r"""Fine-lattice version of the round-7 resonance model (round7/interpolation/resonance_model.py).

Question: the round-7 model L ~ P(Y), Y = U^{-m1 (s-a)}, realizes the count corner (dip of the
Moebius profile on (r*, t*)).  For FIXED degree d its log-derivative -L'/L = sum_n p_n Y^n has
"prime mass" only at the discrete scales U^{n m1}, so its prime sums vanish at generic slot scales:
the model would sit in amplitude class p ~ 0, not in the binding class p = 1/2.
Does the model survive when the lattice is refined (d ~ log U, m1 ~ 1/log U), so that every slot
scale is hit?  Checked here:
  (a) max |coeff| of P and of 1/P (= A/(1+cY^{k2}), A of degree k1 = k2 - d) stays O(1);
  (b) the power sums p_n = sum_{j in S} zeta_j^{-n} (the model's von Mangoldt mass per scale block,
      in units of a single isolated zero) are >~ 1 for the slot range n <= 0.505 d
      (slot scales up to U^{0.209}: n m1 <= 0.209, m1 = m*/d).
Coefficients are computed by FFT on a circle |Y| = rho < 1 (stable for large d).
"""
import numpy as np

MSTAR, TSTAR = 0.41399, 1.15527   # corner of PR69 face C at delta = 0.4546, p = 1/2


def beatty_roots(d, k2, c=1.0):
    zeta = np.exp(1j*(np.pi + 2*np.pi*np.arange(k2))/k2) * (1/c)**(1/k2)   # roots of 1 + c Y^k2
    S = sorted({int(np.floor(j*k2/d)) for j in range(d)})
    assert len(S) == d
    notS = [j for j in range(k2) if j not in set(S)]
    return zeta, S, notS


def coeffs_by_fft(roots, deg, M=None, rho=None):
    """coefficients of prod_{z in roots}(1 - Y/z), degree deg, via FFT on |Y| = rho."""
    if M is None:
        M = 1 << int(np.ceil(np.log2(8*(deg + 1))))
    if rho is None:
        rho = 1 - 1/(20*(deg + 1))
    Y = rho*np.exp(2j*np.pi*np.arange(M)/M)
    logv = np.zeros(M, dtype=complex)
    for z in roots:
        logv += np.log(1 - Y/z)
    vals = np.exp(logv)
    c = np.fft.fft(vals)/M            # c[n] = coeff_n * rho^n  (sign convention of fft: sum v e^{-2pi i kn/M})
    n = np.arange(M)
    coef = c/rho**n
    return coef[:deg + 1]


def run(d):
    k2 = int(round(d*TSTAR/MSTAR))
    k1 = k2 - d
    zeta, S, notS = beatty_roots(d, k2)
    P = coeffs_by_fft(zeta[S], d)
    A = coeffs_by_fft(zeta[notS], k1)
    p = np.array([np.sum(zeta[S]**(-n)) for n in range(1, k2)])
    nslot = int(0.505*d)
    ps = np.abs(p[:nslot])
    return dict(d=d, k2=k2, k1=k1, r=k1*MSTAR/d, t=k2*MSTAR/d,
                maxP=np.abs(P).max(), maxA=np.abs(A).max(),
                lead=(abs(P[0]), abs(P[-1]), abs(A[0]), abs(A[-1])),
                slot_min=ps.min(), slot_med=np.median(ps), slot_frac_lt_half=(ps < 0.5).mean(),
                slot_frac_lt_tenth=(ps < 0.1).mean())


if __name__ == "__main__":
    print("check against round-7 small d (expect max coeffs <= 1):")
    for d in (5, 9, 14, 24, 43):
        o = run(d)
        print(f"  d={d:3d} k2={o['k2']:4d}  max|P|={o['maxP']:.3f} max|A|={o['maxA']:.3f}  "
              f"slot range n<= {int(0.505*d)}: min|p_n|={o['slot_min']:.3f} median={o['slot_med']:.3f} "
              f"frac(|p_n|<0.5)={o['slot_frac_lt_half']:.2f}")
    print("fine lattice:")
    for d in (100, 200, 400, 800, 1600):
        o = run(d)
        print(f"  d={d:4d} k2={o['k2']:5d}  max|P|={o['maxP']:.3f} max|A|={o['maxA']:.3f}  "
              f"lead/trail |P0|,|Pd|,|A0|,|Ak1| = {tuple(round(x,3) for x in o['lead'])}  "
              f"slots: min|p_n|={o['slot_min']:.3f} median={o['slot_med']:.3f} "
              f"frac<0.5={o['slot_frac_lt_half']:.2f} frac<0.1={o['slot_frac_lt_tenth']:.2f}")


def run_coprime(d):
    """same as run(), but with k2 adjusted to be coprime to d (a periodic Beatty set S makes
    p_n vanish identically for n not divisible by gcd(d, k2); that is an artifact)."""
    from math import gcd
    k2 = int(round(d*TSTAR/MSTAR))
    while gcd(k2, d) != 1:
        k2 += 1
    k1 = k2 - d
    zeta, S, notS = beatty_roots(d, k2)
    P = coeffs_by_fft(zeta[S], d)
    A = coeffs_by_fft(zeta[notS], k1)
    p = np.array([np.sum(zeta[S]**(-n)) for n in range(1, k2)])
    ps = np.abs(p[:int(0.505*d)])
    # slot windows: a smooth dyadic slot covers log 2 of log-scale; with c' = m1 log U the model
    # scales are spaced c'; take c' = log 2 / 2 (two model scales per slot window) as a test.
    win = np.array([abs(p[n] + p[n+1]) for n in range(len(ps) - 1)])
    return d, k2, np.abs(P).max(), np.abs(A).max(), ps.min(), np.median(ps), (ps < 0.1).mean(), win.min(), np.median(win)


if __name__ == "__main__":
    print("coprime k2:")
    for d in (100, 200, 400, 800, 1600, 3200):
        d_, k2, mP, mA, mn, med, f01, wmin, wmed = run_coprime(d)
        print(f"  d={d_:4d} k2={k2:5d} max|P|={mP:.3f} max|A|={mA:.3f}  single-scale |p_n|: min={mn:.4f} "
              f"median={med:.3f} frac<0.1={f01:.2f}   two-scale window |p_n+p_n+1|: min={wmin:.4f} median={wmed:.3f}")
