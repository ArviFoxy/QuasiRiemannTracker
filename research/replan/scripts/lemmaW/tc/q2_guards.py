# guard values (Collet vs Lemma W) of the C and capped branches at the binding point of PR 86
from fractions import Fraction as Fr
import pr86, cert_return as CR
base = pr86.Cfg(th=Fr(8739558,10**7))
def evalpoly(a, dl, p):
    return sum(float(c)*dl**i*p**j for (i,j),c in a.items())
for win in ('collet','lemmaW'):
    cfg = base.copy(windows=win)
    pr86.apply_globals(cfg)
    G = pr86.geometry(cfg)
    cands = {nm:(br,meta) for nm,br,meta in pr86.candidate_list(cfg,G)}
    print('=== windows', win)
    for name in ('C','Pcap'):
        br, meta = cands[name]
        B,L,s_plus,capped = meta
        polys, scal = CR.admission_polys(br,B,L,s_plus,capped)
        for dl,p in ((0.4415,0.5),(0.40,0.5),(0.38,0.5),(0.45,0.5),(0.4415,0.45)):
            D=evalpoly(br['D'],dl,p); J=evalpoly(br['J'],dl,p); Mn=evalpoly(br['Mn'],dl,p); DJ=D*J
            mstar = Mn/DJ    # plain crossing m*
            r = evalpoly(br['Rn'],dl,p)/DJ
            print('  %-5s delta=%.4f p=%.2f: m*=%.5f  r*(Rn/DJ)=%.5f   guards(min over 12 poly, listed):' % (name,dl,p,mstar,r), end=' ')
            g = {k:evalpoly(q,dl,p) for k,q in polys.items()}
            kmin = min(g, key=lambda k: g[k]/ (abs(DJ) if k in ('Mn-mLDJ','mUDJ-Mn','N-tail','cap') else 1) ) 
            print('Mn-mLDJ/DJ=%.4f mUDJ-Mn/DJ=%.4f N-tail/J=%.4f' % (g['Mn-mLDJ']/DJ, g['mUDJ-Mn']/DJ, g['N-tail']/J), {k:round(float(v),5) for k,v in scal.items()})
