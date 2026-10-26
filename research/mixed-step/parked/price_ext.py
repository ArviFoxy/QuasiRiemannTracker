"""Pricing of C beyond the family on the extended flow (QRH_FLOW_EXT): the C cap needed, then the best h.
P fixed at its exact face (QRH_FACES). usage: (source return_cut.env) QRH_FLOW_EXT=... python3 price_ext.py S1,S2,..."""
import os, sys
from fractions import Fraction as Fr
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import theta_star as T
import price_faces as PF
W = Fr(29, 500)
P = T.faces()[1]
for s in sys.argv[1].split(','):
    B, L = PF.flow_face(Fr(s))
    caps = {}
    for cap in ('86/1000', '88/1000', '90/1000', '92/1000', '94/1000', '96/1000'):
        caps[cap] = T.theta_star(((B, L, Fr(cap)), P), Fr(8061, 10000), W, W, 'lemmaD', 8740800)
    sat = min(caps.values())
    need = next(c for c in caps if caps[c] == sat)
    print(f'C s={s} B={float(B):.7f} L={float(L):.7f}: theta* at h=0.8061 by cap ' +
          ', '.join(f'{float(Fr(c)):.3f}:{caps[c]/1e7:.7f}' for c in caps) + f'  -> cap {float(Fr(need)):.3f} suffices', flush=True)
    res = []
    for h in ('8057/10000', '8058/10000', '8059/10000', '806/1000', '8061/10000', '8062/10000', '80625/100000'):
        t = T.theta_star(((B, L, Fr(96, 1000)), P), Fr(h), W, W, 'lemmaD', 8740800)
        why = T.certifiable(Fr(t - 1, 10**7), ((B, L, Fr(96, 1000)), P), Fr(h), W, W, 'lemmaD', why=True)[1]
        res.append((t, h, why))
    t, h, why = min(res)
    print(f'   best over h (cap 0.096): theta* = {t/1e7:.7f} at h = {float(Fr(h))}  [{why}]; all: ' +
          ', '.join(f'{float(Fr(hh))}:{tt/1e7:.7f}' for tt, hh, _ in res), flush=True)
