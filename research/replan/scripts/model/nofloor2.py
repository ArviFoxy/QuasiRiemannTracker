import sys
sys.path.insert(0,'$SCRATCH/analysis/model')
from fast import *
from scipy.integrate import solve_ivp
DL,P=grids()
base=mk86()
def rhs(L,y):
    B=y[0]; q=0.999*L/(6*B-L); return [(B-10/(15-6*q))/(L-1)]
sol=solve_ivp(rhs,[2.5715,2.0],[0.99999],rtol=1e-12,atol=1e-14,dense_output=True)
def face(L): return float(sol.sol(L)[0]),L
def theta2(fc,fp,pointwise=False):
    r=copy.deepcopy(base)
    r.faces={'C':Face(fc[0],fc[1],0.09999,False),'capP':Face(fp[0],fp[1],0.062,True)}
    r.physB,r.physL=fp
    kw=dict(pointwise=True) if pointwise else {}
    c,h,s,rr=solve_c_fast(r,iters=18,DL=DL,P=P,hspan=0.03,clo=0.12,chi=0.13,**kw)
    cw=rr.check_windows(n=31)
    return 1-c,[(i+1,w[0]) for i,(w,m,j) in enumerate(cw) if m<=0]
for Lc in [2.30,2.27,2.25,2.22,2.20,2.15]:
    fc=face(Lc); 
    th,bad=theta2(fc,face(2.371))
    thp,_=theta2(fc,face(2.371),pointwise=True)
    print('no-floor ODE role split: C@%.3f (B=%.5f, s0=%.4f) P@2.371 -> theta(Sil windows)=%.9f bad=%s | pointwise %.9f'%(Lc,fc[0],rhs(Lc,[fc[0]])[0],th,bad,thp),flush=True)
