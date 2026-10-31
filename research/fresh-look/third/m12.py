# For several K: price the width-restricted count face (jump guard) and the selected-norm saving Delta it needs (under C)
import sys, io, contextlib
with contextlib.redirect_stdout(io.StringIO()):
    from m10 import env_restricted, theta, PR99, bar
    from kwlib import run_from_base, worst_geo3
K = float(sys.argv[1]); s0 = float(sys.argv[2])
Lend, cend, why, path = run_from_base(K)
def needed(Lstop):
    pth = [q for q in path if q[0] >= Lstop - 1e-9]
    idx = sorted(set([1] + [int(len(pth)*f) for f in (0.2, 0.4, 0.6, 0.8)] + [len(pth)-1]))
    def passes(D):
        for i in idx:
            L, c, a = pth[i]; L0, c0, _ = pth[i-1]
            v, wh = worst_geo3(0.99999, L, c, a, L0, c0, K, D, s0)
            if v > 0: return False
        return True
    if passes(0.0): return 0.0, pth[-1]
    lo, hi = 0.0, 0.12
    for _ in range(9):
        mid = (lo+hi)/2
        if passes(mid): hi = mid
        else: lo = mid
    return hi, pth[-1]
print('K=%.2f line end L=%.4f (%s)' % (K, Lend, why), flush=True)
for Lq in (1.94, 1.92, 1.90):
    if Lq < Lend: continue
    D, (L, c, a) = needed(Lq)
    t = theta(env_restricted(L, c, s0, mode='strict')[0])[0]
    print('  K %.2f s0 %.3f stop L %.4f cap %.4f: theta-bar %+.2e  needed Delta %.4f' % (K, s0, L, c, t - bar, D), flush=True)
