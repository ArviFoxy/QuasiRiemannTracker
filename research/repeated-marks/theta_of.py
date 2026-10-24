"""Float estimate of the final theta for a chain file (C = pivot 0.04232 node, P = pivot ~0.0395 node)."""
import sys, os, json, numpy as np
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import model69 as M
from pick_theta2 import maxc
def fval(x): return float(Fr(x)) if isinstance(x, str) else float(x)
def faces(path, pC=0.04232, pP=0.0395):
    ch = json.load(open(path))
    nC = min(ch, key=lambda n: abs(float(n['pivot'])-pC)); nP = min(ch, key=lambda n: abs(float(n['pivot'])-pP))
    return (fval(nC['B']), fval(nC['L'])), (fval(nP['B']), fval(nP['L']))
def best_theta(C, P, hs=np.linspace(0.7994, 0.8010, 17), sP=1/25, grid=(401, 201)):
    FC = M.Face(C[0], C[1], 11/250, 'C'); FP = M.Face(P[0], P[1], 43/1000, 'P')
    dl, pp = M.grid(*grid)
    best = (0, None)
    for h in hs:
        c, o = maxc(FC, FP, h, sP, dl, pp)
        if c > best[0]: best = (c, h)
    return 1-best[0], best[1]
if __name__ == "__main__":
    for path in sys.argv[1:]:
        C, P = faces(path)
        th, h = best_theta(C, P)
        print(f"{path}: C={C} P={P} theta~{th:.9f} h={h:.5f}", flush=True)
