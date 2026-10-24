"""Quantitative targets: how much each binding atom must move to lower theta by 1e-5.

Float model of the final return (Collet FR13 / NR1-NR7) with a generic LP count:
  I(r) = 1 - delta*(r + 2 p zI(r)),  zI(r) = (mI - r)/sI        (marked inverse moment: r + sI z <= mI)
  L(r) = (aL + bL r)/6 - delta r - epsL  for r > 1              (long Mobius moment, default (1+5r)/6)
  P(m) = 1 - 2 delta m - 2 delta p zP(m), zP(m) = min(cap, (B - 2m)/Lam)   (plain face C)
  R(delta,p) = min_t max_{r<=t, r+m>=t, m<=1/2} min(I or L at r, P at m)
Return exponent at conductor d with capacity C(d) (P face):
  E = 1/2 + 13h/75 - y/2 - l/2 - 9d/100 + delta/2 + delta p (l - C/2) + (3d/4) R
Geometry from the physical bound theta = k + x/2 + cg (y - x), k = 5/6 - x/3 - l/6, x + y = 1 - l,
x = 1 + l - h (cg = 1/12 gives l = 11/3 - 4 theta).
The natural count and the admission windows are omitted; this is a sensitivity model, not a certificate.
"""
import numpy as np, sys

BASE = dict(mI=1.0, sI=2.0, aL=1.0, bL=5.0, epsL=0.0, BC=0.9564652291, LC=2.9005114226, capC=13/250,
            BP=0.9610063016, LP=3.0106108488, sP=9/200, cg=1/12, h=401/500)

def count(delta, p, P):
    # grids for t (cutoff), r (inverse length)
    ts = np.linspace(1.0, 1.5, 251)
    best = np.full(np.shape(delta), np.inf)
    for t in ts:
        rs = np.linspace(0.0, t, 401)
        r = rs[:, None, None]; d = delta[None]; pp = p[None]
        m = np.maximum(t - r, 0)
        zI = np.clip((P['mI'] - r)/P['sI'], 0, None)
        I = 1 - d*(r + 2*pp*zI)
        L = (P['aL'] + P['bL']*r)/6 - d*r - P['epsL']
        inv = np.where(r <= 1, I, L)
        zP = np.clip(np.minimum(P['capC'], (P['BC'] - 2*m)/P['LC']), 0, None)
        Pl = np.where(m <= 0.5, 1 - 2*d*m - 2*d*pp*zP, -np.inf)   # m > 1/2 cannot occur (saturation)
        worst = np.max(np.minimum(inv, Pl), axis=0)
        best = np.minimum(best, worst)
    return best

def old_count(kappa, delta, p):
    V = 5/6 - delta
    D = 3 - p - 2*p/(3*kappa)
    C = 2*(1-p)*(1 - p/(3*kappa))
    J = V*D + delta*C
    N = (1-delta)*J + delta*C*V/2
    return N/J

def geometry(theta, P):
    h, cg = P['h'], P['cg']
    # theta = 5/6 + (1-h)/6 + cg (2h - 3l - 1)
    l = (2*h - 1 - (theta - 5/6 - (1 - h)/6)/cg)/3
    x = 1 + l - h; y = h - 2*l; kap = 2*theta - 1
    return l, x, y, kap

def gap(theta, P, dl, pp, R):
    l, x, y, kap = geometry(theta, P)
    h = P['h']; BP, LP, sP = P['BP'], P['LP'], P['sP']
    ds = 2*y/(1 + 6*kap*sP); dk = 2*y/(2 - BP + LP*sP); dp = h
    CO = lambda d: min(d, 2*y - d)/(6*kap)
    CN = lambda d: min(sP*d, (2*y - (2 - BP)*d)/LP)
    edges = [(1/200, CO(1/200)), (y, CO(y)), (ds, CO(ds)), (ds, CN(ds)), (dp, CN(dp))]
    if dk < dp: edges.append((dk, CN(dk)))
    worst = -np.inf
    for d, C in edges:
        Rs = np.minimum(R, old_count(kap, dl, pp))
        E = 0.5 + 13*h/75 - y/2 - l/2 - 9*d/100 + dl/2 + dl*pp*(l - C/2) + 0.75*d*Rs
        worst = max(worst, np.max(E - theta))
    return worst

def theta_star(P, nd=226, npp=21):
    dl, pp = np.meshgrid(np.linspace(0.30, 0.75, nd), np.linspace(0.30, 0.5, npp), indexing='ij')
    R = count(dl, pp, P)
    lo, hi = 0.8740, 0.8752
    for _ in range(40):
        mid = (lo + hi)/2
        if gap(mid, P, dl, pp, R) <= 0: hi = mid
        else: lo = mid
    return hi

if __name__ == "__main__":
    base = theta_star(BASE)
    print(f"base theta* (float LP model) = {base:.8f}", flush=True)
    tests = [('mI', +1e-3), ('sI', -1e-2), ('epsL', +1e-3), ('bL', -1e-2), ('BC', +1e-3), ('LC', -1e-2),
             ('BP', +1e-3), ('LP', -1e-2), ('cg', -1e-3)]
    for k, dv in tests:
        P = dict(BASE); P[k] = BASE[k] + dv
        th = theta_star(P)
        need = 1e-5/abs(th - base)*abs(dv) if th != base else float('inf')
        print(f"{k:5s} {BASE[k]:+.6f} -> {P[k]:+.6f}: dtheta = {th - base:+.3e};  change needed for -1e-5: {need:.2e}",
              flush=True)
