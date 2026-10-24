"""Value of information per source-step gate: rebuild the K=8 chain with selected gates disabled,
then report the envelope heights at s=0.0412 (physical) and 0.0449 (count) and the float theta*."""
import sys, json, time
import numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/repeated-marks')
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/atom-targets')
drop = set(sys.argv[1].split(',')) if sys.argv[1] != 'none' else set()
out = sys.argv[2]
import ss_fb
_g = ss_fb.gates_at
def gates_at(*a, **k):
    g = _g(*a, **k)
    for key in list(g.keys()):
        if any(key == d or key.startswith(d) for d in drop):
            g[key] = (1.0, 0.0) if isinstance(g[key], tuple) else 1.0
    return g
ss_fb.gates_at = gates_at
import cchain_k as CK
CK.gates_at = gates_at
t0 = time.time()
piv = [round(0.0135 + 0.0005*i, 4) for i in range(58)] + [0.04232]
capf = lambda s: min(0.0549989, round(s + 0.016, 7))
nodes = CK.build(piv, capf, 8, verbose=False)
json.dump(nodes, open(out, 'w'), indent=1)
fl = lambda s: float(Fr(s))
env = lambda s: max(fl(n['B']) - fl(n['L'])*s for n in nodes if fl(n['cap']) >= s)
print(f"drop={sorted(drop)}: {len(nodes)} nodes, {time.time()-t0:.0f}s, env(0.0412)={env(0.0412):.6f} env(0.0449)={env(0.0449):.6f}", flush=True)
cands = [n for n in nodes if fl(n['cap']) >= 0.0521]
nC = max(cands, key=lambda n: fl(n['B']) - fl(n['L'])*0.045)
nP = max([n for n in nodes if fl(n['cap']) >= 0.045], key=lambda n: (fl(n['B']) - 0.83666)/fl(n['L']))
import targets as T
P = dict(T.BASE); P.update(BC=fl(nC['B']), LC=fl(nC['L']), BP=fl(nP['B']), LP=fl(nP['L']))
dl, pp = np.meshgrid(np.linspace(0.30, 0.75, 226), np.linspace(0.30, 0.5, 21), indexing='ij')
R = T.count(dl, pp, P)
lo, hi = 0.8735, 0.8755
for _ in range(40):
    mid = (lo+hi)/2
    if T.gap(mid, P, dl, pp, R) <= 0: hi = mid
    else: lo = mid
print(f"RESULT drop={sorted(drop)} theta*={hi:.8f}  C=({fl(nC['B']):.6f},{fl(nC['L']):.5f}) P=({fl(nP['B']):.6f},{fl(nP['L']):.5f})", flush=True)
