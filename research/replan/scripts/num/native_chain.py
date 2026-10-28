from fractions import Fraction as F
K = F(3,4)
def gates(pB,pL,pc, nB,nL,nc, a):
    g = {}
    g['retention'] = a - K*(pL-nL+(6*pB-pL)*a)/pL
    g['cap'] = pc*(1-6*a*nc)-(1-a)*nc
    g['principal'] = nL-2-F(9,2)*a
    g['diagonal'] = nL-1-4*a
    g['secondRef'] = F(3,2)*nL-F(5,2)-F(9,2)*a
    g['refPos'] = F(1,6)-(1+F(3,2)*a)*nc
    g['H'] = 1-6*a*nc
    g['overshoot'] = 1-K*(6*pB-pL)/pL
    g['B_le'] = pB-nB
    g['B_lt'] = 1-pB
    g['cap_lt'] = F(1,6)-pc
    g['cap_pos'] = nc
    g['a_pos'] = a
    g['L_lt'] = pL-nL
    return g
faces = [(F(99999,100000),F(93,25),F(3,50)),
         (F(9999,10000),F(31,10),F(3,50)),
         (F(9999,10000),F(29,10),F(67,1000)),
         (F(9999,10000),F(14,5),F(73,1000)),
         (F(9999,10000),F(68,25),F(79,1000))]
avals = [F(6,25),F(9,50),F(3,20),F(31,200)]
print("explicit 4 steps:")
for i in range(4):
    g = gates(*faces[i],*faces[i+1],avals[i])
    assert all(v>0 for v in g.values()) or True
    tight = sorted(g.items(), key=lambda kv: kv[1])[:4]
    print(i, "min gates:", [(k,float(v)) for k,v in tight], "all ok:", all((v>=0 if k=='B_le' else v>0) for k,v in g.items()))
Bg = F(9999,10000); Ls = 18*Bg/7
L = F(68,25); c = F(79,1000)
print("L* =", float(Ls))
a = F(3,25)
allpos=True
for n in range(22):
    Ln = Ls + F(43,50)*(L-Ls)
    cn = c/(F(47,50)+F(9,25)*c)
    g = gates(Bg,L,c,Bg,Ln,cn,a)
    ok = all((v>=0 if k=='B_le' else v>0) for k,v in g.items())
    allpos &= ok
    tight = sorted(g.items(), key=lambda kv: kv[1])[:3]
    print(n, "L=%.6f c=%.6f"%(float(Ln),float(cn)), "tight:", [(k,round(float(v),5)) for k,v in tight], ok)
    L, c = Ln, cn
print("geoL22 =", float(L), "<2.58:", L<F(129,50), " geoC22 =", float(c), ">0.12:", c>F(3,25), "allpos", allpos)
