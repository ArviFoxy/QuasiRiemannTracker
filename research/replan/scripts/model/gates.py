"""Python model of Sil's HybridGates (PR83 Source/HybridGates.lean) for one density-split transition.
Faithful transcription of the gate functions at lines 31-95 and the HybridGates structure at 114-138."""
import re, numpy as np
from fractions import Fraction as Fr

SUB = '$SCRATCH/upstream/submissions'

def frac(s):
    s = s.strip().strip("'")
    return Fr(s)

def parse_chain(path=SUB + '/2026-10-28-density-split-fine-chain/src/Submissions/density_split_fine_chain/Source'):
    rows = []
    for i in range(1, 47):
        txt = open(f'{path}/HybridK15_{i:02d}.lean').read().split('\n')[:4]
        t = ' '.join(txt)
        m = re.search(r"parent G\(('[^']+'), ('[^']+'), ('[^']+')\) -> child G\(('[^']+'), ('[^']+'), ('[^']+')\), selection A = ([0-9/]+), D = ([0-9/]+)", t)
        g = [frac(x) for x in m.groups()]
        rows.append(dict(i=i, B0=g[0], L0=g[1], c0=g[2], B=g[3], L=g[4], c=g[5], A=g[6], D=g[7]))
    return rows

def rho(nu):
    return 1 - 10 * nu / (15 - 6 * nu)

def gate_values(B0, L0, c0, B, L, c, A, D, v=None, n=4001, floor=0.65, qmin=0.5, qmax=0.75, hmin=0.9, dfac=0.999):
    B0, L0, c0, B, L, c, A, D = [float(x) for x in (B0, L0, c0, B, L, c, A, D)]
    s0 = (B0 - B) / (L0 - L)
    vmax = c - s0
    if v is None:
        v = np.linspace(0.0, vmax, n)
    w = s0 + v
    u = A * v / (1 + D * v)
    E = (L0 - L) * (1 + D * v) + (6 * B0 - L0) * A
    q = dfac * L0 * A / E
    H = 1 - 6 * u
    J = 1 - rho(q) - q * B + q * (L - 1) * w - (6 * (1 - rho(q)) - q - 1) * u
    g = {}
    g['q_lower'] = q - qmin
    g['q_upper'] = qmax - q
    g['q_floor'] = q - floor
    g['H_lower'] = H - hmin
    g['retained_cap'] = c0 * H - (w - u)
    g['retained_width'] = w - u
    g['low_per_width'] = 0.001 * L0 * A / (1 + D * v)
    g['high_at_q'] = J
    g['high_deriv'] = 25 / 24 * H - (B - (L - 1) * w - u)
    g['principal'] = 1 - B + (L - 2) * w - 4.5 * u
    g['second_ref'] = 0.05 + 1.5 * (1 - B) + (1.5 * L - 2.5) * w - 4.5 * u
    g['second_diag'] = 1 - B + (L - 1) * w - 4 * u
    g['ref_upper'] = 1 / 3 - 2 * w - 3 * u
    g['sel_deriv'] = A / (1 + D * v) ** 2
    return s0, vmax, v, g, dict(q=q, u=u, w=w, H=H)

def gate_mins(*args, **kw):
    s0, vmax, v, g, aux = gate_values(*args, **kw)
    return s0, vmax, {k: (float(val.min()), float(v[val.argmin()])) for k, val in g.items()}

def feasible(*args, tol=0.0, **kw):
    s0, vmax, v, g, aux = gate_values(*args, **kw)
    if vmax <= 0 or s0 < 0:
        return False
    return all(val.min() > tol for val in g.values())
