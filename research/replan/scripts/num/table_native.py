from fractions import Fraction as F
K=F(3,4)
Bg=F(9999,10000); Ls=18*Bg/7
rows=[]
faces=[(F(99999,100000),F(93,25),F(3,50)),(F(9999,10000),F(31,10),F(3,50)),(F(9999,10000),F(29,10),F(67,1000)),(F(9999,10000),F(14,5),F(73,1000)),(F(9999,10000),F(68,25),F(79,1000))]
avals=[F(6,25),F(9,50),F(3,20),F(31,200)]
def ret(pL,nL,pB,a): return float(a-K*(pL-nL+(6*pB-pL)*a)/pL)
out=[]
out.append("| step | a | child face G(B, L, c) | retention reserve | note |")
out.append("|---|---|---|---|---|")
out.append("| init | - | (0.99999, 3.72, 0.06) | - | PR76 actual_global_source |")
for i in range(4):
    p,n=faces[i],faces[i+1]
    out.append("| %d | %s | (%.4f, %.3f, %.3f) | %.4f | explicit gates0%d%d |" % (i+1, avals[i], float(n[0]),float(n[1]),float(n[2]), ret(p[1],n[1],p[0],avals[i]), i, i+1))
L=F(68,25); c=F(79,1000)
for n in range(22):
    Ln=Ls+F(43,50)*(L-Ls); cn=c/(F(47,50)+F(9,25)*c)
    out.append("| %d | 3/25 | (0.9999, %.5f, %.5f) | %.5f | geometric n=%d->%d |" % (5+n, float(Ln), float(cn), ret(L,Ln,Bg,F(3,25)), n, n+1))
    L,c=Ln,cn
out.append("| (sub) | - | (0.9999, 2.58, 0.12) | - | bootstrapFace = Face.Sub of geoFace 22 |")
print("\n".join(out))
