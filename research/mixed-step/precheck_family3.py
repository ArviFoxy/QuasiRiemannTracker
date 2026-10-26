"""Pre-check the mixed family certificates in Python (covers and HIGH trees) before the Lean data
extraction finishes: every pos1I cover and every HIGH tree must exist.
usage: QRH_K=9/2 python3 precheck_family3.py [pieces]"""
import sys, time
import gen_family3 as G
import polyq as P
import ipoly as I
import gen_faceless_I as GI

fam, fan = G.build()
pcs = [int(x) for x in sys.argv[1].split(',')] if len(sys.argv) > 1 else range(len(fam.H))
for j in pcs:
    t0 = time.time()
    for p in G.field3P(fam, j):
        G.cover1(p)
    if j in G.CAPRAMP:
        for p in G.capField(fam, j):
            G.cover1(p)
    for e in (0, 1):
        b = G.endP3(fam, j, e)
        for p in G.sg3N(fam, j, b):
            G.cover1(p)
        G.cover1(G.weak3N(fam, j, b))
        G.cover1(G.cell3N(fam, j, b))
        for s3 in range(3):
            for p in G.sec3B(fam, j, b, s3):
                G.cover1(p)
    print(f"piece {j}: scalar covers ok ({time.time()-t0:.1f}s)", flush=True)
    for e in (0, 1):
        for k in [(i, jj) for i in range(2) for jj in range(3)]:
            t0 = time.time()
            U = G.highU3(fam, j, G.endP3(fam, j, e), k)
            U = [[P.trim(U[a][bb]) for bb in range(4)] for a in range(4)]
            Dd, c = I.to_int16(U)
            T = GI.find_I(c, 0, 0, 0, 1)
            print(f"piece {j} high {e} {k}: {'ok' if T is not None else 'FAIL'} {GI.stats_I(T) if T else ''} ({time.time()-t0:.1f}s)", flush=True)
