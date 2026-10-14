import numpy as np
from scipy.optimize import minimize_scalar
L=19312/4787; Bc=1419985639/1436100000
m_lo=(Bc-L/25)/2; m_hi=847/2000
dl=np.linspace(0,.75,751)[:,None]; P=np.linspace(0,.5,401)[None,:]
def Rold(k,d,p):
    den=3*k*(3-p)-2*p; c=2*(1-p)*(3*k-p)/den; rd=(5/6-d)+d*c
    return 1-d+d*c*(5/6-d)/(2*rd)
def Rnew_valid(d,p,gam=1e-4):
    V=5/6-d; DN=3-p-4*p/L; aN=2-4*p/L; cN=1-2*p*Bc/L; J=V*DN+d*(1-p)*aN
    t=(V*DN+d*(1-p)*(aN+cN))/J; R=1-d+V*d*(1-p)*cN/J
    r=(aN*t+2*p*Bc/L-p)/DN; m=t-r; sh=1-d*(p+(1-p)*r)
    Pold=1-2*d*m_hi-2*d*p*(1-2*m_hi)/(6*.75)
    ok=(r>=23/37)&(r<=1)&(m>=m_lo+gam)&(Pold<=sh-1e-5)&(t>=1)&(t<=1.5)
    return R,ok
RN,OK=Rnew_valid(dl,P)
def margin(th,h,use_new=True):
    ell=11/3-4*th; y=h-2*ell; k=2*th-1
    R=Rold(k,dl,P)
    if use_new: R=np.where(OK,np.minimum(R,RN),R)
    out=[]
    for d,C,v in ((h,(2*y-(2-Bc)*h)/L,1e-6),(h-1e-3,min(h-1e-3,2*y-h+1e-3)/(6*k),1e-5),(.5,min(.5,2*y-.5)/(6*k),1e-3)):
        G=(1+dl)/2+13*h/75-y/2-ell/2+ell*dl*P+d*(1/4+3*R/4-17/50)-dl*P*C/2
        out.append(th-v-G.max())
    return min(out)
def hcap(th):
    ell=11/3-4*th
    nm=(Bc-0.037*L)/2
    return min((4*ell-1.16e-3)/0.84,(2*ell-(1-nm)*1e-3)/nm)
def best(th,cap=True,use_new=True):
    hi=hcap(th) if cap else .80
    r=minimize_scalar(lambda h:-margin(th,h,use_new),bounds=(.785,hi),method='bounded',options={'xatol':1e-9})
    return -r.fun,r.x
def thmin(cap,use_new):
    lo,hi=.8747,.87490
    for _ in range(30):
        mid=(lo+hi)/2; m,h=best(mid,cap,use_new)
        if m>=0: hi=mid; hb=h
        else: lo=mid
    return hi,hb
for cap in (False,True):
    for un in (False,True):
        th,h=thmin(cap,un); print('cap',cap,'new',un,'theta_min %.8f h %.7f hcap %.6f'%(th,h,hcap(th)))
