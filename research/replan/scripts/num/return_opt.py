import numpy as np
from scipy.optimize import minimize, brentq
from return_replica import Faces, Ret, slack, EPS7
import copy

def worst_need(r, n=401, refine=True):
    """max over edges, (delta,p) of min over available branches of needed; returns (value, edge, delta, p, branch)"""
    worst, out = slack(r, n)
    best = max(((v[0],e,v[1],v[2],v[3]) for e,v in worst.items()), key=lambda t:t[0])
    if not refine: return best
    val,e,dl,p,b = best
    # local refinement on a fine local grid
    h = 0.75/(n-1)
    dls = np.linspace(max(0,dl-3*h), min(0.75,dl+3*h), 241)
    ps = np.linspace(max(0,p-3*0.5/(n-1)), min(0.5,p+3*0.5/(n-1)), 241)
    DL,P = np.meshgrid(dls,ps,indexing='ij')
    cand = r.needed(e,'old',DL,P)
    for b2 in ['C','capP']:
        adm = r.admitted(b2,DL,P)
        nd = r.needed(e,b2,DL,P)
        cand = np.where(adm & (nd<cand), nd, cand)
    i = np.unravel_index(np.argmax(cand), cand.shape)
    return (cand[i], e, DL[i], P[i], b)

if __name__=='__main__':
    F = Faces()
    r = Ret(25201/200000, 8053/10000, F)
    val,e,dl,p,b = worst_need(r)
    print("actual constants: worst need %.10f on %s at delta=%.5f p=%.5f (%s); theta-reserve=%.10f; slack=%+.3e" % (val,e,dl,p,b,r.theta-F.reserve,r.theta-F.reserve-val))
    # also report need of each branch at that point
    for bb in ['old','C','capP']:
        if bb=='old': print("  old need", r.needed(e,'old',np.array(dl),np.array(p)))
        else:
            print("  %s need %.10f admitted=%s" % (bb, r.needed(e,bb,np.array(dl),np.array(p)), bool(r.admitted(bb,np.array(dl),np.array(p)))))
