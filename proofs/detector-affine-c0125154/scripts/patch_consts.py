from fractions import Fraction as F
import re,sys,os
def q(v): return f"{v.numerator}/{v.denominator}"
def consts(th,h):
    ell=F(11,3)-4*th; x=1+ell-h; y=h-2*ell; ks=2*th-1
    dm=h-F(1,1000); dp=h+F(1,10**10); d0=F(1,200); t0=F(1,1000)
    LAM=F(19312,4787); B=F(14200,14361)-F(1,100000)
    nmin=1-y/dm; nmax=1-y/dp+t0
    zmin=(B-2*nmax)/LAM; zmax=(B-2*nmin)/LAM
    Dlow=F(5,2)-1/(3*ks)
    return dict(
      supply_lower=ell/dp-F(4,21), supply_half=2*ell-F(1,3), supply_four=4*ell-y,
      lower_row=th-(F(7,8)-49*h/150+7*ell/8+33*d0/50), floor=th-(F(51,100)+h/3+51*ell/100),
      new_feedback=5*dp/288, principal_y=y/20-(1+h)/1000-F(1,4000), principal_h=h/600-F(1,1000)-F(1,4000),
      marked_tuple=-(1+3*ell-2*(x+y)), marked_short=-(y-2*x+ell),
      Dlow=Dlow, Jlow=Dlow/12,
      junction=(2*y-(2-B)*dm)/LAM-(2*y-dm)/(6*ks),
      nmin=nmin,nmax=nmax,zmin=zmin,zmax=zmax,
      cap_supply=ell-dp*zmax, bmax=2*y/dm-1, y_dm=y/dm, y_dp=y/dp, theta=th)
old=consts(F(874861,1000000),F(3969737987,5000000000))
new=consts(F(437423,500000),F(15903,20000))
for k in old: print(k, q(old[k]), '->', q(new[k]), float(new[k]))
# replacement pairs (old string -> new string)
pairs=[(q(old[k]),q(new[k])) for k in old if k not in ('theta',)]
pairs.append(("874861/1000000","437423/500000")); pairs.append(("874861 / 1000000","437423 / 500000"))
# note: old string forms in Lean may have spaces " / "
root=sys.argv[1]
changed={}
for dirpath,_,files in os.walk(root):
    for fn in files:
        if not fn.endswith('.lean'): continue
        p=os.path.join(dirpath,fn); s=open(p).read(); s0=s
        for a,b in pairs:
            for aa,bb in ((a,b),(a.replace('/',' / '),b.replace('/',' / '))):
                if aa in s:
                    changed.setdefault(fn,[]).append(aa); s=s.replace(aa,bb)
        if s!=s0: open(p,'w').write(s)
for k,v in changed.items(): print(k, v)
