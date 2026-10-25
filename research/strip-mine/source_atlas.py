"""Source-side sensitivity atlas: perturb the continuum flow's ingredients, rebuild the end faces
from Sil's tangency, and score them with the exact return (theta*, units 1e-7).

Knobs (relative bumps):
  q6:<literal>  literals of the HIGH-threshold closed form 6q_p (closed_flow.q6star), instrumented
  LOW6          the LOW exchange rate 6 in the flow slope (Q = 6q -> LOW6/6 * 6q)
  B0, lam       Sil's start face (0.99999, 93/25)
  qfloor        the HIGH density floor 1/2
  den, phi      the step's LOW denominator and slope reserve
usage: python3 source_atlas.py EPS NPROC"""
import os, sys, ast, types, json, time
import numpy as np
from fractions import Fraction as Fr
from multiprocessing import Pool
from scipy.optimize import brentq
HERE = os.path.dirname(os.path.abspath(__file__))
FC = os.path.join(HERE, '..', 'faceless-chain')
sys.path.insert(0, FC); sys.path.insert(0, HERE)
import atlas as A          # exact return driver (BASE, theta_star)

REL = {}
def KN(name, v): return v*(1 + REL.get(name, 0.0))

class R(ast.NodeTransformer):
    def __init__(self): self.knobs = []
    def visit_FunctionDef(self, node):
        if node.name != 'q6star': return node
        self.generic_visit(node); return node
    def visit_Constant(self, node):
        if isinstance(node.value, (int, float)) and not isinstance(node.value, bool) and node.value not in (0, 0.0):
            name = f"q6:{node.lineno}:{node.col_offset}:{node.value}"
            self.knobs.append(name)
            return ast.copy_location(ast.Call(ast.Name('KN', ast.Load()), [ast.Constant(name), ast.Constant(node.value)], []), node)
        return node

def load_q6():
    src = open(os.path.join(FC, 'closed_flow.py')).read()
    tree = ast.parse(src); rw = R(); tree = rw.visit(tree); ast.fix_missing_locations(tree)
    m = types.ModuleType('cf_knobs'); m.KN = KN; m.np = np
    exec(compile(tree, os.path.join(FC, 'closed_flow.py'), 'exec'), m.__dict__)
    return m, rw.knobs

CF, Q6KNOBS = load_q6()
CAP = Fr(549989, 10**7)

def family():
    B0, lam = KN('B0', 0.99999), KN('lam', 3.72)
    den, phi, qf = KN('den', 2**-15), KN('phi', 1e-4), KN('qfloor', 0.5)
    low6 = KN('LOW6', 6.0)/6.0
    def slope(s, E):
        q = max(CF.q6star(s, E)[0]/6, qf)
        Q = low6*6*q
        return Q*E/((1 - Q*s)*(1 - den))*(1 + phi), q
    g = lambda s: slope(s, B0 - lam*s)[0] - lam
    s0 = brentq(g, 1e-4, 0.0599, xtol=1e-14) if g(1e-4) > 0 else 1e-4
    E, s, out = B0 - lam*s0, s0, []
    h = (0.06 - s0)/20000
    for _ in range(20000):
        L, q = slope(s, E); out.append((s, E, L, q, E + L*s))
        f = lambda s_, E_: -slope(s_, E_)[0]
        k1 = f(s, E); k2 = f(s + h/2, E + h*k1/2); k3 = f(s + h/2, E + h*k2/2); k4 = f(s + h, E + h*k3)
        E += h*(k1 + 2*k2 + 2*k3 + k4)/6; s += h
    end = next((i for i, o in enumerate(out) if o[3] <= qf + 1e-9), len(out) - 1)
    C = out[end]
    P = next((o for o in reversed(out[:end + 1]) if o[2] >= 3.0), out[0])
    fr = lambda x: Fr(x).limit_denominator(10**12)
    return dict(A.BASE, BC=fr(C[4]*(1 - 2e-9)), LC=fr(C[2]), BP=fr(P[4]*(1 - 2e-9)), LP=fr(P[2])), (s0, C[0], P[0])

def job(args):
    name, eps, base = args
    REL.clear()
    if name: REL[name] = eps
    t = time.time()
    P, where = family()
    th = A.theta_star(P, guess=base if base else 8746075)
    return dict(name=name, eps=eps, theta=th, delta=None if (th is None or base is None) else th - base,
                s0=where[0], sC=where[1], sP=where[2], secs=round(time.time() - t, 1))

if __name__ == '__main__':
    eps, nproc = float(sys.argv[1]), int(sys.argv[2])
    A.init()
    b = job(('', 0.0, None)); base = b['theta']
    print('base', json.dumps(b), flush=True)
    names = [k for k in Q6KNOBS if int(k.split(':')[1]) <= 12] + ['LOW6', 'B0', 'lam', 'qfloor', 'den', 'phi']
    out = []
    with Pool(nproc, initializer=A.init) as pool:
        for r in pool.imap_unordered(job, [(n, eps, base) for n in names]):
            out.append(r); print(json.dumps(r), flush=True)
    out.sort(key=lambda r: -abs(r['delta'] or 0))
    json.dump(dict(base=base, eps=eps, results=out), open(os.path.join(HERE, f'source_atlas_eps{eps:g}.json'), 'w'), indent=1)
