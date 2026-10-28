import numpy as np
from return_replica import Faces, Ret
F=Faces(); r=Ret(25201/200000,8053/10000,F)
names = ["D>0","A>0","C0>0","J>0","T-J>0","1.2499J-T>0","RN-(23/37)DJ>0","DJ-RN>0","MN-lowerM*DJ>0","upperM*DJ-MN>0","N-(natural tail)J>0","U*dJ-dU*J>0","11/25-natM>0","B-2natM-L(s-)>0","(Z-s-)DJ>0"]
for b in ['C','capP']:
    print("branch",b)
    for (dl,p) in [(0.4406,0.5),(0.44,0.5),(0.40,0.5),(0.46,0.5),(0.50,0.5),(0.5,0.45),(0.4406,0.49)]:
        g = r.guards(b,np.array(dl),np.array(p))
        J,N,q = r.parts(b,np.array(dl),np.array(p))
        # normalize by J-scale
        vals = [float(x) for x in g]
        order = np.argsort(np.array(vals)/np.maximum(1e-12,np.abs(vals)+1))
        neg = [names[i] for i,x in enumerate(vals) if x<=0]
        small = sorted([(abs(x),names[i],x) for i,x in enumerate(vals)])[:3]
        print("  (delta=%.4f,p=%.3f): admitted=%s ; failing=%s ; 3 smallest |guard|: %s" % (dl,p,len(neg)==0,neg,[(n,round(x,6)) for _,n,x in small]))
