"""Raise the natural seed cap h0 (Collet: 'any required fixed h0 is permitted by its natural
capacity inequality') and rebuild the K=8 chain with caps min(h0 - 1e-6, s + off)."""
import sys, json, time
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/repeated-marks')
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/atom-targets')
h0 = float(sys.argv[1]); off = float(sys.argv[2]); out = sys.argv[3]
pmax = float(sys.argv[4]) if len(sys.argv) > 4 else 0.04232
import cchain_k as CK
def build(pivots, capf, K):
    par_f = (1.0, CK.K_FB, h0)
    par_q = (Fr(1), Fr(11243277, 2500000), Fr(str(h0)))
    nodes = []
    for s in pivots:
        cap = capf(s)
        sol = CK.solve(par_f, s, cap, K)
        if sol is None:
            continue
        Lam, q = sol
        LamQ = CK.dec(Lam + 2e-12, up=True)
        Bq = CK.dec(float(par_q[0] - (par_q[1]-LamQ)*Fr(str(s))), up=False)
        qQ = CK.dec(q, nd=12)
        capQ = Fr(str(cap))
        if not CK.ok(float(Bq), float(LamQ), float(qQ), par_f, float(capQ), K, nnu=801, res=CK.RES/2):
            continue
        nodes.append(dict(B=str(Bq), L=str(LamQ), q=str(qQ), cap=str(capQ), pivot=s))
        par_f = (float(Bq), float(LamQ), float(capQ)); par_q = (Bq, LamQ, capQ)
    return nodes
t0 = time.time()
n = int(round((pmax - 0.0135)/0.0005))
piv = [round(0.0135 + 0.0005*i, 4) for i in range(n+1)]
if 0.04232 not in piv and pmax >= 0.04232: piv = sorted(set(piv + [0.04232]))
capf = lambda s: min(h0 - 1e-6, round(s + off, 7))
nodes = build(piv, capf, 8)
json.dump(nodes, open(out, 'w'), indent=1)
fl = lambda s: float(Fr(s))
def env(s):
    c = [fl(x['B']) - fl(x['L'])*s for x in nodes if fl(x['cap']) >= s]
    return max(c) if c else float('nan')
print(f"h0={h0} off={off}: {len(nodes)} nodes, last pivot {nodes[-1]['pivot'] if nodes else None}, {time.time()-t0:.0f}s, env(0.0412)={env(0.0412):.6f} env(0.0449)={env(0.0449):.6f}", flush=True)
cands = [x for x in nodes if fl(x['cap']) >= 0.0521]
pc = [x for x in nodes if fl(x['cap']) >= 0.045]
nC = max(cands, key=lambda x: fl(x['B']) - fl(x['L'])*0.045)
nP = max(pc, key=lambda x: (fl(x['B']) - 0.83666)/fl(x['L']))
import targets as T
P = dict(T.BASE); P.update(BC=fl(nC['B']), LC=fl(nC['L']), BP=fl(nP['B']), LP=fl(nP['L']))
dl, pp = np.meshgrid(np.linspace(0.30, 0.75, 226), np.linspace(0.30, 0.5, 21), indexing='ij')
R = T.count(dl, pp, P)
lo, hi = 0.8735, 0.8755
for _ in range(40):
    mid = (lo+hi)/2
    if T.gap(mid, P, dl, pp, R) <= 0: hi = mid
    else: lo = mid
print(f"RESULT h0={h0} off={off} theta*={hi:.8f}  C=({fl(nC['B']):.6f},{fl(nC['L']):.5f},cap {fl(nC['cap']):.4f}) P=({fl(nP['B']):.6f},{fl(nP['L']):.5f},cap {fl(nP['cap']):.4f})", flush=True)
