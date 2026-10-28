"""Greedy density-split chain with a configurable q-floor (replica of PR83 Source/HybridGates.lean:62-95, 114-138).
Runs from the end of PR 86's chain, per-step optimising (A,D) for the smallest crossing slope s0 subject to every
gate >= eps, and reports the binding gate.  NOT a Lean check."""
import sys, json, numpy as np
from scipy.optimize import minimize

def rho(nu): return 1-10*nu/(15-6*nu)

GATES = ['q_lower','q_upper','q_floor','H_lower','retained_cap','retained_width','low','high_at_q','high_deriv',
         'principal','second_ref','second_diag','ref_upper','sel_deriv']

def gmin(B0,L0,c0,B,L,c,A,D,floor,N=400,qmin=0.5,qmax=0.75,hmin=0.9,dfac=0.999):
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

SCALEFREE=('low','sel_deriv')
def worst(B0,L0,c0,B,L,c,A,D,floor,eps):
    m,s0,vmax=gmin(B0,L0,c0,B,L,c,A,D,floor)
    if m is None: return -1.0,None,None
    best=None;bk=None
    for k,x in m.items():
        val = (x if x<=0 else 1.0) if k in SCALEFREE else x-eps
        if best is None or val<best: best,bk=val,k
    return best,bk,m

def s0_min(B0,L0,c0,dL,c,A,D,floor,eps):
    L=L0-dL
    hi=c-1e-4
    xs=np.linspace(1e-5,hi,100)
    ok=[worst(B0,L0,c0,B0-s*dL,L,c,A,D,floor,eps)[0]>=0 for s in xs]
    if not any(ok): return None
    i=ok.index(True)
    if i==0: return xs[0]
    a,b=xs[i-1],xs[i]
    for _ in range(40):
        mid=0.5*(a+b)
        if worst(B0,L0,c0,B0-mid*dL,L,c,A,D,floor,eps)[0]>=0: b=mid
        else: a=mid
    return b

def best_step(B0,L0,c0,dL,c,floor,eps,guess):
    def f(x):
        A=np.exp(x[0]); D=np.exp(x[1])
        s=s0_min(B0,L0,c0,dL,c,A,D,floor,eps)
        return 1.0 if s is None else s
    best=None
    starts=[guess]+[(np.log(a),np.log(d)) for a in (0.3,0.5,0.8,1.2) for d in (5,20,80,300)]
    for st in starts:
        r=minimize(f,np.array(st),method='Nelder-Mead',options=dict(xatol=1e-4,fatol=1e-9,maxiter=200))
        if best is None or r.fun<best.fun: best=r
        if st is guess and best.fun<0.9: break
    return best.fun,float(np.exp(best.x[0])),float(np.exp(best.x[1]))

def run(floor,dL,Lend,eps=1e-6,B0=0.9888151,L0=2.3415,c0=0.1,c=0.1,guess=(np.log(0.5),np.log(22.0)),out=None):
    rows=[]
    k=0
    while L0-dL>=Lend-1e-12:
        s,A,D=best_step(B0,L0,c0,dL,c,floor,eps,guess)
        if s>=0.9:
            rows.append(dict(k=k+1,infeasible=True,B0=B0,L0=L0)); break
        B=B0-s*dL; L=L0-dL
        # binding gate just beyond optimum, and all gate minima at the step
        b,bk,m=worst(B0,L0,c0,B,L,c,A,D,floor,eps)
        k+=1
        q0=0.999*L0*A/((L0-L)+(6*B0-L0)*A)
        vmax=c-s
        qm=0.999*L0*A/((L0-L)*(1+D*vmax)+(6*B0-L0)*A)
        rows.append(dict(k=k,B0=B0,L0=L0,B=B,L=L,s0=s,A=A,D=D,q0=q0,qmax=qm,bind=bk,mins=m))
        if out: print(json.dumps(rows[-1]),file=out,flush=True)
        guess=(np.log(A),np.log(D)); B0,L0,c0=B,L,c
    return rows

if __name__=='__main__':
    floor=float(sys.argv[1]); dL=float(sys.argv[2]); Lend=float(sys.argv[3])
    rows=run(floor,dL,Lend)
    for r in rows:
        if r.get('infeasible'): print('k=%d INFEASIBLE from L0=%.4f B0=%.6f'%(r['k'],r['L0'],r['B0'])); continue
        sm=sorted(r['mins'].items(),key=lambda kv:kv[1])[:3]
        print('k=%2d L=%.4f B=%.6f s0=%.5f A=%.3f D=%.2f q(0)=%.4f q(vmax)=%.4f bind=%s | %s'%(
            r['k'],r['L'],r['B'],r['s0'],r['A'],r['D'],r['q0'],r['qmax'],r['bind'],
            ' '.join('%s=%.2e'%(k,v) for k,v in sm)),flush=True)
