import sys
FLOOR = [0.65]
import numpy as np
from scipy.optimize import minimize, brentq, minimize_scalar

def rho(nu): return 1-10*nu/(15-6*nu)

def gmin(B0,L0,c0,B,L,c,A,D,N=500,floor=None,qmin=0.5,qmax=0.75,hmin=0.9,dfac=0.999):
    """minimum over v of every gate (vectorised, cubic grid dense near v=0); returns dict of minima, s0, vmax"""
    floor = FLOOR[0] if floor is None else floor
    s0=(B0-B)/(L0-L); vmax=c-s0
    if vmax<=0: return None,s0,vmax
    t=np.linspace(0,1,N)**3
    v=vmax*t
    w=s0+v; u=A*v/(1+D*v)
    E=(L0-L)*(1+D*v)+(6*B0-L0)*A
    q=dfac*L0*A/E
    H=1-6*u
    J=1-rho(q)-q*B+q*(L-1)*w-(6*(1-rho(q))-q-1)*u
    g=dict(q_lower=q-qmin,q_upper=qmax-q,q_floor=q-floor,H_lower=H-hmin,retained_cap=c0*H-(w-u),
           retained_width=w-u,low=0.001*L0*A/(1+D*v),high_at_q=J,high_deriv=25/24*H-(B-(L-1)*w-u),
           principal=1-B+(L-2)*w-4.5*u,second_ref=0.05+1.5*(1-B)+(1.5*L-2.5)*w-4.5*u,
           second_diag=1-B+(L-1)*w-4*u,ref_upper=1/3-2*w-3*u,sel_deriv=A/(1+D*v)**2)
    return {k:float(val.min()) for k,val in g.items()},s0,vmax

def worst(B0,L0,c0,B,L,c,A,D,eps=0.0,**kw):
    m,s0,vmax=gmin(B0,L0,c0,B,L,c,A,D,**kw)
    if m is None: return -1.0,None
    # scale-free: low/sel_deriv gates only need >0 (tiny natural scale) -> do not count them against eps
    vals=[]
    for k,x in m.items():
        if k in ('low','sel_deriv'): vals.append(x if x<=0 else 1.0)
        else: vals.append(x-eps)
    k=min(m,key=lambda kk: (m[kk]-eps if kk not in ('low','sel_deriv') else (m[kk] if m[kk]<=0 else 1.0)))
    return min(vals),k

def s0_min(B0,L0,c0,dL,c,A,D,eps=1e-6,N=500,lo=0.0,hi=None):
    """smallest slope s0 (largest child B) for which all gates >= eps, for fixed A,D. scan then bisect. returns None if none"""
    L=L0-dL
    hi=hi if hi is not None else c-1e-4
    xs=np.linspace(lo+1e-5,hi,120)
    ok=[worst(B0,L0,c0,B0-s*dL,L,c,A,D,eps,N=N)[0]>=0 for s in xs]
    if not any(ok): return None
    i=ok.index(True)
    if i==0: return xs[0]
    a,b=xs[i-1],xs[i]
    for _ in range(40):
        mid=0.5*(a+b)
        if worst(B0,L0,c0,B0-mid*dL,L,c,A,D,eps,N=N)[0]>=0: b=mid
        else: a=mid
    return b

def best_step(B0,L0,c0,dL,c,eps=1e-6,guess=None,N=400,verbose=False):
    """optimise (A,D) to minimise s0. returns (s0,A,D)"""
    def f(x):
        A=np.exp(x[0]); D=np.exp(x[1])
        s=s0_min(B0,L0,c0,dL,c,A,D,eps,N)
        return 1.0 if s is None else s
    best=None
    starts=[guess] if guess is not None else []
    starts+= [(np.log(a),np.log(d)) for a in (0.4,0.6,0.8) for d in (20,100,400)]
    for st in starts:
        r=minimize(f,np.array(st),method='Nelder-Mead',options=dict(xatol=1e-4,fatol=1e-9,maxiter=150))
        if best is None or r.fun<best.fun: best=r
        if guess is not None and best.fun<0.9: break
    return best.fun,float(np.exp(best.x[0])),float(np.exp(best.x[1]))
