import sys, time
from fractions import Fraction as Fr
import mirror3 as M, cover3
from exact_run import buildK, windows
Lend = Fr(sys.argv[1]) if len(sys.argv) > 1 else Fr(101, 50)
pcap = Fr(sys.argv[2]) if len(sys.argv) > 2 else Fr(12, 100)
capL = Fr(1, 10) + Fr(3, 50) * (Fr(5143, 2000) - Lend)
consts = dict(mMinus=Fr(3, 10), sMinus=Fr(1, 10000), eleven=Fr(1, 2))
M.set_constants(**consts)
des = dict(cB=Fr(99999, 100000), cL=Lend, cCap=capL, w=Fr(1, 100), pB=Fr(99999, 100000), pL=Lend, pCap=pcap, numCap=Fr(3, 40))
plos = [Fr(0), Fr(1, 4), Fr(3, 8), Fr(7, 16), Fr(15, 32), Fr(31, 64), Fr(63, 128), Fr(127, 256), Fr(255, 512)]
th_est = {Fr(101, 50): 0.873432378, Fr(401, 200): 0.873411973, Fr(20001, 10000): 0.873405237}.get(Lend, 0.8734)
N0 = int((1 - th_est) * 5e7) - 10
K, th, h = buildK(N0, des)
O = cover3.Oracle(K)
ws = windows(O, consts, ('C', 'capC', 'capP'), plos)
best = None
for N in range(N0, N0 + 20):
    K, th, h = buildK(N, des)
    ok, res = cover3.Oracle(K).run(ws, edges=['newTop'])
    if ok: best = N
    else: break
K, th, h = buildK(best, des)
O = cover3.Oracle(K)
ok, res = O.run(ws)
used = sorted(set(i for e in res for i in res[e]['used']))
small = [ws[i] for i in used]
# greedy drop
changed = True
while changed:
    changed = False
    for i in range(len(small)):
        trial = small[:i] + small[i + 1:]
        if cover3.Oracle(K).run(trial, edges=['newTop'])[0]:
            small = trial; changed = True; break
ok2, res2 = cover3.Oracle(K).run(small, verbose=True)
print('Lend', Lend, 'pCap', pcap, 'BEST N', best, 'theta = %.8f' % float(1 - Fr(best, 50000000)), 'h =', h, 'all edges', ok2)
print('windows (%d):' % len(small))
for w in small: print('   ', w[0], w[1], w[2], w[3], '(%.5f-%.5f)' % (float(w[1]), float(w[2])))
