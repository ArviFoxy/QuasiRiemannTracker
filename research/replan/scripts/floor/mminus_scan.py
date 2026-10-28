import sys, copy
sys.path.insert(0,'$SCRATCH/analysis/model')
from fast import *
DL,P=grids()
base=mk86()
PFACE=(0.9907142,2.3715)
def theta(fc,fp,mm):
    r=copy.deepcopy(base)
    r.faces={'C':Face(fc[0],fc[1],0.09999,False),'capP':Face(fp[0],fp[1],0.062,True)}
    r.physB,r.physL=fp
    r.mMinus=mm
    c,h,s,rr=solve_c_fast(r,iters=18,DL=DL,P=P,hspan=0.03,clo=0.12,chi=0.13)
    cw=rr.check_windows(n=31)
    bad=[(i+1,w[0]) for i,(w,m,j) in enumerate(cw) if m<=0]
    return 1-c,bad
fc=(0.978722,2.2065)
for mm in (0.377,0.37,0.36,0.35,0.34,0.33):
    th,bad=theta(fc,PFACE,mm)
    print('floor-0.60 step27 face C=(%.6f,%.4f) P=%s mMinus=%.3f -> theta=%.9f bad=%s'%(fc[0],fc[1],PFACE,mm,th,bad),flush=True)
