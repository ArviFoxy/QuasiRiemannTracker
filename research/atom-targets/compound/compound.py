"""Compounded sensitivity: rebuild the source chain with modified HIGH-count atoms and evaluate the
float return model with the same atoms.
  c     : marked-inverse slot cost (r + c z <= Q)        (2 in the paper)
  epsL  : improvement of the long line exponent (Q+5t)/6 - nu t - epsL   (0 in the paper)
usage: python3 compound.py c epsL out.json"""
import sys, os, json, time
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/repeated-marks')
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/atom-targets')
import gain_fast as GF

c = float(sys.argv[1]); epsL = float(sys.argv[2]); out = sys.argv[3]

def f_all(nu, S, F, ps, K, BL, al=5/6):
    B, Lam, hc = BL
    p = ps[:, None]; nu_ = nu[None, :]
    kk = al - nu_
    # inverse cap with slot cost c: r + 2p (F - r)/c >= xi  ->  r >= (xi - 2pF/c)/(1 - 2p/c)
    den = 1 - 2*p/c
    inv = [(1/den, (2*p*F/c)/den)]
    if K is not None:
        inv.append((np.ones_like(p), 2*p*K*S))
    pl = [(np.ones_like(p), 2*p*S), (np.ones_like(p), 2*p*hc*F),
          (1/(1-2*p/Lam), (2*p*B*F/Lam)/(1-2*p/Lam))]
    roots = None
    for (ai, bi) in inv:
        for (aj, bj) in pl:
            r = (al*F + epsL + kk*(bi + bj/2))/(nu_ + kk*(ai + aj/2))
            roots = r if roots is None else np.minimum(roots, r)
    xi0F = al*F/(nu_ + 1.5*kk)
    return (1-2*p)*nu_*S + nu_*(roots - xi0F)

GF.f_all = f_all
import cchain_k as CK
CK.gain = GF.gain

t0 = time.time()
piv = [round(0.0135 + 0.0005*i, 4) for i in range(58)] + [0.04232]
capf = lambda s: min(0.0549989, round(s + 0.016, 7))
nodes = CK.build(piv, capf, 8, verbose=False)
json.dump(nodes, open(out, 'w'), indent=1)
print(f"c={c} epsL={epsL}: {len(nodes)} nodes, {time.time()-t0:.0f}s", flush=True)

# faces as in evalchain.py
fl = lambda s: float(Fr(s))
cands = [n for n in nodes if fl(n['cap']) >= 0.0521]
nC = max(cands, key=lambda n: fl(n['B']) - fl(n['L'])*0.045)
nPs = [n for n in nodes if fl(n['cap']) >= 0.045 and fl(n['L']) > 3] or [n for n in nodes if fl(n['cap']) >= 0.045]
nP = max(nPs, key=lambda n: (fl(n['B']) - 0.83666)/fl(n['L']))
print('C face', nC['pivot'], fl(nC['B']), fl(nC['L']), ' P face', nP['pivot'], fl(nP['B']), fl(nP['L']), flush=True)

import targets as T
P = dict(T.BASE)
P.update(BC=fl(nC['B']), LC=fl(nC['L']), BP=fl(nP['B']), LP=fl(nP['L']), sI=c, epsL=epsL)
dl, pp = np.meshgrid(np.linspace(0.30, 0.75, 226), np.linspace(0.30, 0.5, 21), indexing='ij')
R = T.count(dl, pp, P)
lo, hi = 0.8735, 0.8755
for _ in range(40):
    mid = (lo+hi)/2
    if T.gap(mid, P, dl, pp, R) <= 0: hi = mid
    else: lo = mid
print(f"RESULT c={c} epsL={epsL} theta*={hi:.8f}", flush=True)
