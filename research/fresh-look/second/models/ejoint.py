# Joint hybrid-norm diagonal extension e (Z-units), after newpowers/R3_return.md s.3.4:
#   probe x+y = 1-ell+e  ->  ell = 11/3-4theta+e/3 (= 4c-1/3+e/3), y = h-2ell+e
#   inverse budget r+2z <= 1+e/h ;  long line L(t) -> L(t) - (5/6) e/h  (RawMoment gate relaxed)
# Banked design as in opus_fresh/models/combo.py (LP + newTop row). [numerical; re-pricing at the bank geometry]
import numpy as np
from scipy.optimize import linprog, minimize_scalar
from scipy.interpolate import CubicSpline
def V_of_t(t, d, p, B, L, cap, ci, s, e, h, parts):
    mc = (B - L*cap)/2; best = -np.inf
    eI = e/h if 'I' in parts else 0.0; eL = e/h if 'L' in parts else 0.0
    for rp in ('I','Lg'):
        for mp in ('cap','slope'):
            A=[]; b=[]
            def le(cr,cm,cz,rhs): A.append([cr,cm,cz]); b.append(rhs)
            if rp=='I':
                k = d - 2*d*p/ci; le(k,0,1,1-2*d*p/ci*(1+eI)); rlo,rhi = max(t-0.5,23/37), min(t,1.0+eI)
            else:
                le(-(s-d),0,1,1-s-(5/6)*eL); rlo,rhi = max(t-0.5,1.0+eI), t
            if rlo > rhi+1e-15: continue
            if mp=='cap':
                le(0,2*d,1,1-2*d*p*cap); mlo,mhi = 0.0, min(mc,0.5)
            else:
                le(0,2*d-4*d*p/L,1,1-2*d*p*B/L); mlo,mhi = max(mc,0.0), 0.5
            if mlo > mhi+1e-15: continue
            le(-1,-1,0,-t)
            res = linprog(c=[0,0,-1],A_ub=np.array(A),b_ub=np.array(b),bounds=[(rlo,rhi),(mlo,mhi),(None,None)],method='highs')
            if res.status==0: best = max(best,-res.fun)
    return best
def count(d,p,B,L,cap,ci,s,e,h,parts):
    f = lambda t: V_of_t(t,d,p,B,L,cap,ci,s,e,h,parts)
    ts = np.linspace(1.0,1.5,61); vs = np.array([f(t) for t in ts]); i = int(np.argmin(vs))
    r = minimize_scalar(f,bounds=(ts[max(i-1,0)],ts[min(i+1,len(ts)-1)]),method='bounded',options={'xatol':1e-10})
    return min(r.fun, vs[i])
def theta_star(e=0.0, parts='PIL', ci=2.0, cf=2.0, s=5/6, h=0.8097, B=0.99999, numcap=0.075, p=0.5):
    L = 2.0001*cf/2; cap = 0.1+0.06*(5143/2000-2.0001)
    dls = np.round(np.arange(0.34,0.5601,0.01),4)
    cs = CubicSpline(dls,[count(dd,p,B,L,cap,ci,s,e,h,parts) for dd in dls])
    dl = np.linspace(0.34,0.56,22001); cn = cs(dl)
    eP = e if 'P' in parts else 0.0
    lo,hi = 0.870,0.8745
    for _ in range(55):
        th=(lo+hi)/2; c=1-th; ell=4*c-1/3+eP/3; y=h-2*ell+eP; dp=h+1e-10
        C = min(numcap*dp,(2*y-(2-B)*dp)/L)
        row = (0.5+13*h/75-y/2-ell/2-0.09*dp+dl/2+dl*p*(ell-C/2)+0.75*dp*cn).max()
        if row > th-1e-8: lo=th
        else: hi=th
    return hi
if __name__ == "__main__":
    base = theta_star(); print('base %.8f (bank 0.87338228)' % base, flush=True)
    for e in (1e-4, 3e-4, 5e-4, 1e-3):
        out = []
        for parts in ('PIL','P','I','L'):
            t = theta_star(e, parts); out.append('%s %+.2e' % (parts, t-0.87341198))
        print('e=%.0e (vs #97): ' % e + '   '.join(out), flush=True)
