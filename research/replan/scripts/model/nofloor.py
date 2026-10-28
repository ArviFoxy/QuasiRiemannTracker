import sys
sys.path.insert(0,'$SCRATCH/analysis/model')
from fast import *
from scipy.integrate import solve_ivp
DL,P=grids()
base=mk86()
def rhs(L,y):
    B=y[0]; q=0.999*L/(6*B-L); return [(B-10/(15-6*q))/(L-1)]
sol=solve_ivp(rhs,[2.5715,2.0],[0.99999],rtol=1e-12,atol=1e-14,dense_output=True)
for L in [2.3385,2.33,2.32,2.31,2.30,2.28,2.25,2.20]:
    B=float(sol.sol(L)[0]); q=0.999*L/(6*B-L); s0=rhs(L,[B])[0]
    r=mkface(B,L,r0=base)
    out=[]
    for pw in (False,True):
        kw=dict(pointwise=True) if pw else {}
        c,h,s,rr=solve_c_fast(r,iters=18,DL=DL,P=P,hspan=0.03,clo=0.120,chi=0.130,**kw)
        cw=rr.check_windows(n=41)
        bad=[(i+1,w[0]) for i,(w,m,j) in enumerate(cw) if m<=0]
        out.append((1-c,bad))
    print('ODE (no q-floor) L=%.4f B=%.6f s0=%.5f q_inf=%.4f -> theta(Sil windows)=%.9f bad=%d | theta(pointwise)=%.9f'%(L,B,s0,q,out[0][0],len(out[0][1]),out[1][0]),flush=True)
