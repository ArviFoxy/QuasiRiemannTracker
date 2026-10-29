"""Step 3: would another proven chain face (or the envelope over all 131 faces) count better at the binding point?"""
import numpy as np
from scipy.optimize import minimize_scalar
from model import P, count, guard_vals, witness, row_exponent
from chainfaces import chain_faces

Pm = P()
target = Pm.theta - Pm.reserve
faces = chain_faces()


def adm(face, d, p):
    g, _ = guard_vals(Pm, None, d, p, face=face)
    return all(v > 0 for v in g)


def cnt(face, d, p):
    return count(Pm, None, d, p, face=face)


# per face: max over delta of the newTop exponent at p = 1/2, using only that face (uncapped / capped)
res = []
for name, (B, L, cap) in faces.items():
    B, L, cap = float(B), float(L), float(cap)
    for capped in (False, True):
        cap_r = min(cap, 0.09999) if not capped else cap   # return caps sit 1e-5 below the source cap
        face = (B, L, cap_r, capped)
        f = lambda d: -row_exponent(Pm, 'newTop', d, 0.5, cnt(face, d, 0.5))
        r = minimize_scalar(f, bounds=(0.35, 0.6), method='bounded', options=dict(xatol=1e-12))
        res.append((-r.fun, name, capped, r.x, adm(face, r.x, 0.5)))
res.sort()
print('best single faces at p=1/2 (newTop max over delta):')
for v, name, capped, d, ok in res[:8]:
    print(f'  {v:.12f}  {name:12s} capped={capped}  delta*={d:.6f}  admissible={ok}  slack={target - v:+.3e}')

# envelope over all uncapped faces: at each delta, min count over admissible faces
def env_all(d, p):
    best = count(Pm, 'old', d, p)
    for name, (B, L, cap) in faces.items():
        for capped in (False, True):
            face = (float(B), float(L), min(float(cap), 0.09999) if not capped else float(cap), capped)
            c = cnt(face, d, p)
            if c < best and adm(face, d, p):
                best = c
    return best

f = lambda d: -row_exponent(Pm, 'newTop', d, 0.5, env_all(d, 0.5))
ds = np.linspace(0.40, 0.50, 201)
vals = [-f(d) for d in ds]
i = int(np.argmax(vals))
r = minimize_scalar(f, bounds=(ds[max(i - 2, 0)], ds[min(i + 2, len(ds) - 1)]), method='bounded', options=dict(xatol=1e-12))
print(f'envelope over all chain faces: max newTop exponent at p=1/2 = {-r.fun:.12f} at delta={r.x:.6f}; slack={target + r.fun:+.3e}')
