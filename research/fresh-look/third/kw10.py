# uniform selected-norm excess gamma tolerated by the width-floored K-line, stopped at Lstop (team currency: gamma=0 needed without floor)
import sys, time
from kwlib import run_from_base, worst2
K = float(sys.argv[1]); s0 = float(sys.argv[2]); Lstop = float(sys.argv[3])
Lend, cend, reason, path = run_from_base(K)
pth = [q for q in path if q[0] >= Lstop - 1e-9]
idx = sorted(set([1] + [int(len(pth)*f) for f in (0.25, 0.5, 0.75)] + [len(pth)-1]))
def passes(g):
    for i in idx:
        L, c, a = pth[i]; L0, c0, _ = pth[i-1]
        v, wh = worst2(0.99999, L, c, a, L0, c0, K, str(g), s0, nS=41, nt=7)
        if v > 0: return False, (round(L, 4), wh[:3])
    return True, None
t0 = time.time()
lo, hi = 0.0, 0.12
ok0, info0 = passes(0.0)
if not ok0: print('K=%.2f s0=%.3f stop %.4f: fails even at gamma=0 %s' % (K, s0, pth[-1][0], info0)); sys.exit()
for _ in range(7):
    mid = (lo + hi)/2; ok, info = passes(mid)
    if ok: lo = mid
    else: hi = mid
print('K=%.2f s0=%.3f stop L=%.4f: uniform gamma tolerated ~ %.4f (fails at %.4f) [%.0fs]' % (K, s0, pth[-1][0], lo, hi, time.time()-t0), flush=True)
