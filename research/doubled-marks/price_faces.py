"""Final-return c for given count face C and numerator face P using the validated model69."""
import os
HERE = os.path.dirname(os.path.abspath(__file__))
import sys, json, numpy as np
sys.path.insert(0, HERE)
import model69 as M

def best_c(FC, FP, hs=np.linspace(0.7975, 0.8015, 17), nd=376, npp=126):
    dl, pp = M.grid(nd, npp)
    best = (0, None)
    for h in hs:
        lo, hi = 0.1251, 0.1262
        f = lambda c: M.E_minus_theta(c, h, dl, pp, faces=(FC, FP), BP=FP.B, LP=FP.Lam)[0]
        if f(lo) > -1e-9: continue
        for _ in range(34):
            mid = (lo+hi)/2
            if f(mid) <= -1e-9: lo = mid
            else: hi = mid
        if lo > best[0]: best = (lo, h)
    return best

if __name__ == "__main__":
    base = best_c(M.FACE_C, M.FACE_P)
    print("PR69 faces:", base)
    ch = json.load(open(sys.argv[1]))
    # count face: last node (pivot 0.04232); numerator face: node maximizing height at 0.0396
    fc = ch[-1]
    fp = max(ch, key=lambda n: n['B']-n['L']*0.0396)
    FC = M.Face(fc['B'], fc['L'], 11/250, 'C'); FP = M.Face(fp['B'], fp['L'], 43/1000, 'P')
    print("new C", fc['B'], fc['L'], "new P", fp['B'], fp['L'], "pivot", fp['bx'])
    r = best_c(FC, FP)
    print("new faces:", r, "dc = %.3e" % (r[0]-base[0]))
