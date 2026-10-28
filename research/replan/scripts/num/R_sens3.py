import numpy as np
from R_sens2 import RetShift, F
from return_opt import worst_need
from scipy.optimize import brentq
dR=0.02; h=0.8053
f = lambda c: (lambda r:(r.theta-F.reserve)-worst_need(r,n=241,refine=False)[0])(RetShift(c,h,F,dR,True))
c=brentq(f,0.115,0.145,xtol=1e-10)
r=RetShift(c,h,F,dR,True)
from return_replica import slack
DLn=401
import return_replica as rr
# worst per edge in the shifted model
DL,P = rr.grid(DLn)
for e in r.edges():
    best = r.needed(e,'old',DL,P); src=np.zeros_like(DL,dtype=int)
    for bi,b in enumerate(['C','capP'],1):
        adm=r.admitted(b,DL,P); nd=r.needed(e,b,DL,P)
        upd=adm&(nd<best); best=np.where(upd,nd,best); src=np.where(upd,bi,src)
    i=np.unravel_index(np.argmax(best),best.shape)
    print("edge %-9s worst need %.6f at delta=%.3f p=%.3f branch=%s (theta-reserve=%.6f)" % (e,best[i],DL[i],P[i],['old','C','capP'][src[i]], r.theta-F.reserve))
