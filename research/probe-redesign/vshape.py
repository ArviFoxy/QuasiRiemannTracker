import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from genmodel import gapf, best_ell, DL, PP, edges, M, FC, FP
import genmodel as G
for h in [0.7964, 0.7974, 0.7984, 0.7994, 0.8004]:
    ell = best_ell(h)
    th = 11/12 - ell/4
    y = h - 2*ell; kappa = 2*th - 1
    Rs = M.count_envelope(kappa, DL, PP, (FC, FP), M.K_I_FINAL)
    out = []
    for name, d, C in edges(h, ell, y, kappa):
        e = (0.5 + 13*h/75 - y/2 - ell/2 - 9*d/100 + DL/2 + DL*PP*(ell - C/2) + 0.75*d*Rs) - th
        # top-2 local maxima over delta at p=0.5 and global
        i = np.unravel_index(np.argmax(e), e.shape)
        out.append((name, round(d,5), round(C,5), f"{e[i]:.2e}", float(DL[i]), float(PP[i])))
    # also scan delta profile at new_top, p=0.5
    name, d, C = [x for x in edges(h, ell, y, kappa) if x[0]=='new_top'][0]
    e = (0.5 + 13*h/75 - y/2 - ell/2 - 9*d/100 + DL/2 + DL*PP*(ell - C/2) + 0.75*d*Rs) - th
    j = PP.shape[1]-1
    prof = e[:, j]
    # local maxima
    lm = [(float(DL[k,j]), float(prof[k])) for k in range(1,len(prof)-1) if prof[k]>=prof[k-1] and prof[k]>=prof[k+1]]
    print(f"h={h:.4f} ell={ell:.6f} theta={th:.9f}")
    for o in out: print("   ", o)
    print("    new_top p=1/2 local maxima over delta:", [(round(a,4), f"{b:.2e}") for a,b in lm])
