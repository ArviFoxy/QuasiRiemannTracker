"""Compounded sensitivity to the LOW amplifier's sixth-power exchange rate (kamp, 6 in the paper)."""
import sys, json, time
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/repeated-marks')
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/atom-targets')
kamp = float(sys.argv[1]); out = sys.argv[2]
import ss_fb
_g = ss_fb.gates_at
def gates_at(*a, **k):
    k['kamp'] = kamp
    return _g(*a, **k)
ss_fb.gates_at = gates_at
import cchain_k as CK
CK.gates_at = gates_at
def solve(par, s, cap, K):
    B0, L0, h0 = par
    qcap = L0/(kamp*B0)
    qs = qcap*(1-np.geomspace(1e-9, 0.4, 70)); qs = qs[(qs >= 0.5) & (qs <= 0.75)]
    def okL(Lam):
        B = B0-(L0-Lam)*s
        for q in qs:
            if CK.ok(B, Lam, q, par, cap, K): return q
        return None
    grid = L0*(1-np.geomspace(1e-9, 0.45, 90))
    hi = None; lo = None
    for Lc in grid:
        if okL(Lc) is not None: hi = Lc
        elif hi is not None: lo = Lc; break
    if hi is None: return None
    if lo is None: lo = 0.5*L0
    for _ in range(40):
        mid = (lo+hi)/2
        if okL(mid) is not None: hi = mid
        else: lo = mid
    return hi, okL(hi)
CK.solve = solve
t0 = time.time()
piv = [round(0.0135 + 0.0005*i, 4) for i in range(58)] + [0.04232]
capf = lambda s: min(0.0549989, round(s + 0.016, 7))
nodes = CK.build(piv, capf, 8, verbose=False)
json.dump(nodes, open(out, 'w'), indent=1)
print(f"kamp={kamp}: {len(nodes)} nodes, {time.time()-t0:.0f}s", flush=True)
fl = lambda s: float(Fr(s))
cands = [n for n in nodes if fl(n['cap']) >= 0.0521]
nC = max(cands, key=lambda n: fl(n['B']) - fl(n['L'])*0.045)
nPs = [n for n in nodes if fl(n['cap']) >= 0.045 and fl(n['L']) > 3] or [n for n in nodes if fl(n['cap']) >= 0.045]
nP = max(nPs, key=lambda n: (fl(n['B']) - 0.83666)/fl(n['L']))
print('C face', nC['pivot'], fl(nC['B']), fl(nC['L']), ' P face', nP['pivot'], fl(nP['B']), fl(nP['L']), flush=True)
import targets as T
P = dict(T.BASE); P.update(BC=fl(nC['B']), LC=fl(nC['L']), BP=fl(nP['B']), LP=fl(nP['L']))
dl, pp = np.meshgrid(np.linspace(0.30, 0.75, 226), np.linspace(0.30, 0.5, 21), indexing='ij')
R = T.count(dl, pp, P)
lo, hi = 0.8735, 0.8755
for _ in range(40):
    mid = (lo+hi)/2
    if T.gap(mid, P, dl, pp, R) <= 0: hi = mid
    else: lo = mid
print(f"RESULT kamp={kamp} theta*={hi:.8f}", flush=True)
