import sys, io, contextlib
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/fresh-look/second/base_models')
with contextlib.redirect_stdout(io.StringIO()):
    import worth, fast, ideal
import numpy as np
from ideal import face_count
fast.branch = worth.make_branch(5/6); ideal.branch = fast.branch
def binding_info(Bc, Lc, Bp, Lp, h=0.8097, capc=0.16, numCap=0.075):
    d = np.round(np.arange(0.30, 0.60, 0.0005), 6); p = np.round(np.array([0.48, 0.49, 0.495, 0.5]), 6)
    DD, PP = np.meshgrid(d, p, indexing='ij')
    ok, v = face_count(DD, PP, Bc, Lc, capc); env = np.where(ok, v, np.inf)
    lo, hi = 0.86, 0.885
    for _ in range(50):
        th = (lo+hi)/2; c = 1-th; ell = 4*c-1/3; y = h-2*ell; kappa = 1-2*c; dd = h+1e-10
        C = min(numCap*dd, (2*y-(2-Bp)*dd)/Lp)
        e = np.minimum(env, worth.old_count(DD, PP, kappa, 5/6))
        E = 0.5+13*h/75-y/2-ell/2-0.09*dd+DD/2+DD*PP*(ell-C/2)+0.75*dd*e
        if E.max() > th-1e-8: lo = th
        else: hi = th
    gap = E - hi
    rows = []
    for jj, pp in enumerate(p):
        sel = d[gap[:, jj] > -2.35e-4]
        for dl in (sel.min(), d[np.argmax(gap[:, jj])], sel.max()) if len(sel) else ():
            b = fast.branch(np.array([dl]), np.array([pp]), Bc, Lc, capc, np.array([False]))
            m = (b['MN']/b['DJ'])[0]; z = (Bc - 2*m)/Lc
            rows.append((pp, dl, m, z))
    return hi, rows
for Lc in (2.0001, 1.9185, 1.8906):
    th, rows = binding_info(0.99999, Lc, 0.99999, 2.0001)
    print('count Lambda %.4f: theta %.8f' % (Lc, th))
    for r in rows: print('   p %.3f delta %.4f  m* %.4f  z(m*) %.4f' % r)
    print('   C/h physical:', ((0.99999 - 2*(1 - (0.8097 - 2*(4*(1-th) - 1/3))/0.8097))/2.0001))
