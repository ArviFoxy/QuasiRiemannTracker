import re, numpy as np
from fractions import Fraction as Fr
from return_replica import Faces, Ret
src = open('$SCRATCH/upstream/submissions/2026-10-26-sil-density-split/src/Submissions/sil_density_split_20261026/Return/Windows.lean').read()
wins=[]
for m in re.finditer(r'def returnWindow(\d+) : ReturnCountWindow where\s+branch := \.(\w+)\s+nonold := by decide\s+deltaLo := \((\S+):ℝ\)\s+deltaHi := \((\S+):ℝ\)\s+pLo := \((\S+):ℝ\)', src):
    n,b,dlo,dhi,plo = m.groups()
    wins.append((int(n),b,float(Fr(dlo)),float(Fr(dhi)),float(Fr(plo))))
print(len(wins),"windows parsed")
for w in wins: print("  window%02d %-4s delta in [%.5f, %.5f]  p in [%.5f, 0.5]" % w)
F=Faces(); r=Ret(25201/200000,8053/10000,F)
n=801
dl=np.linspace(0,0.75,n); p=np.linspace(0,0.5,n)
DL,P=np.meshgrid(dl,p,indexing='ij')
# availability from the explicit boxes only
avail={'C':np.zeros_like(DL,bool),'capP':np.zeros_like(DL,bool)}
for (k,b,dlo,dhi,plo) in wins:
    avail[b] |= (DL>=dlo-1e-12)&(DL<=dhi+1e-12)&(P>=plo-1e-12)
# compare to guard-based availability
for b in ['C','capP']:
    g = r.admitted(b,DL,P)
    print("branch %-4s: boxes cover %d pts; guards-admitted %d pts; boxes ⊄ guards: %d ; guards\\boxes: %d" % (b, avail[b].sum(), g.sum(), (avail[b]&~g).sum(), (g&~avail[b]).sum()))
for e in r.edges():
    best=r.needed(e,'old',DL,P); src_=np.zeros_like(DL,int)
    for bi,b in enumerate(['C','capP'],1):
        nd=r.needed(e,b,DL,P); upd=avail[b]&(nd<best); best=np.where(upd,nd,best); src_=np.where(upd,bi,src_)
    i=np.unravel_index(np.argmax(best),best.shape)
    print("edge %-9s worst need %.9f  slack %+.3e  at delta=%.4f p=%.4f via %s" % (e,best[i],r.theta-F.reserve-best[i],DL[i],P[i],['old','C','capP'][src_[i]]))
