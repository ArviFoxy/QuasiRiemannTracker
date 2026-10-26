"""Pointwise view of the binding: for each count branch at an edge, the return polynomial F_b and the
admission polynomials at points (delta, p).  usage: python3 probe_point.py theta_1e7 edge d1,d2,... [p]"""
import sys
from fractions import Fraction as Fr
import base as B
CR = B.CR

def ev(poly, d, p):
    return sum(c * d**i * p**j for (i, j), c in poly.items())

def main():
    th = int(sys.argv[1]); edge = sys.argv[2]
    ds = [Fr(x) for x in sys.argv[3].split(',')]
    p = Fr(sys.argv[4]) if len(sys.argv) > 4 else Fr(1, 2)
    P = B.params(sys.argv[5] if len(sys.argv) > 5 else '')
    G = CR.geometry(Fr(th, 10**7), P['h'], P['BP'], P['LP'], P['sP'])
    E = {n: (d, C) for n, d, C in CR.edges(G, P['BP'], P['LP'])}
    d, C = E[edge]
    print(f"edge {edge}: d={float(d):.6f} C={float(C):.6f}  (s_P h={float(P['sP']*d):.6f})")
    cands = CR.candidates({'C': (P['BC'], P['LC'], P['sC']), 'P': (P['BP'], P['LP'], P['sPp'])}, G['kap'])
    for dl in ds:
        row = []
        for name, br, meta in cands:
            if '-' in name: continue
            rp = CR.return_poly(br, G, d, C)
            F = ev(rp, dl, p); J = ev(br['J'], dl, p); R = ev(br['N'], dl, p)/J
            adm = ''
            if meta is not None:
                polys, scal = CR.admission_polys(br, *meta)
                bad = [k for k, q in polys.items() if ev(q, dl, p) <= 0] + [k for k, v in scal.items() if v <= 0]
                adm = 'ADM' if not bad else 'no:' + ','.join(bad)
            row.append(f"{name}: R={float(R):.6f} F/J={float(F/J):+.3e} {adm}")
        print(f"delta={float(dl):.5f}: " + ' | '.join(row))

if __name__ == '__main__':
    main()
