import sys
sys.path.insert(0,'$SCRATCH/analysis/model')
from fast import *
DL,P=grids()
base=mk86()
def theta_of(r,**kw):
    c,h,s,rr=solve_c_fast(r,iters=18,DL=DL,P=P,hspan=0.03,**kw)
    cw=rr.check_windows(n=41)
    bad=[(i+1,w[0],round(m,5),j) for i,(w,m,j) in enumerate(cw) if m<=0]
    return 1-c,bad
th0,_=theta_of(base); print('base',th0,flush=True)
for capP in [0.062,0.07,0.08,0.09,0.09999]:
    r=copy.deepcopy(base); r.faces['capP']=Face(r.faces['capP'].B,r.faces['capP'].L,capP,True); r.numeratorCap=min(r.numeratorCap,capP)
    th,bad=theta_of(r); print('capP cap=%.5f -> theta=%.9f (%+.2e) badwin=%s'%(capP,th,th-th0,bad),flush=True)
for capC in [0.09999,0.12,0.14]:
    r=copy.deepcopy(base); r.faces['C']=Face(r.faces['C'].B,r.faces['C'].L,capC,False)
    th,bad=theta_of(r); print('countCap=%.5f -> theta=%.9f (%+.2e) badwin=%s'%(capC,th,th-th0,bad),flush=True)
for sm in [0.02,0.03,0.04]:
    r=copy.deepcopy(base); r.sMinus=sm
    th,bad=theta_of(r); print('sMinus=%.3f -> theta=%.9f (%+.2e) badwin=%s'%(sm,th,th-th0,bad),flush=True)
for nc in [0.05,0.06,0.07,0.09]:
    r=copy.deepcopy(base); r.numeratorCap=nc
    th,bad=theta_of(r); print('numeratorCap=%.3f -> theta=%.9f (%+.2e) badwin=%s'%(nc,th,th-th0,bad),flush=True)
for dm in [0.7,0.76,0.8]:
    r=copy.deepcopy(base); r.dm=dm
    th,bad=theta_of(r); print('dm=%.2f -> theta=%.9f (%+.2e) badwin=%s'%(dm,th,th-th0,bad),flush=True)
