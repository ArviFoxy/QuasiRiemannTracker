# failure geometry of the floored K=0.45 line under a uniform excess just above tolerance
from kwlib import run_from_base, worst2
K = 0.45
Lend, cend, reason, path = run_from_base(K)
pth = [q for q in path if q[0] >= 1.90 - 1e-9]
for s0, g in ((0.118, 0.049), (0.118, 0.06), (0.0, 0.002), (0.0, 0.01)):
    worstv = None
    for i in sorted(set([1, len(pth)//4, len(pth)//2, 3*len(pth)//4, len(pth)-1])):
        L, c, a = pth[i]; L0, c0, _ = pth[i-1]
        v, wh = worst2(0.99999, L, c, a, L0, c0, K, str(g), s0, nS=41, nt=7)
        if worstv is None or v > worstv[0]: worstv = (v, round(L, 4), wh)
    print('s0 %.3f gamma %.3f: worst %+.2e at L %.4f  (S, s, M, x1, x2, sel, par, u) = %s' % ((s0, g) + worstv[:2] + (worstv[2],)), flush=True)
