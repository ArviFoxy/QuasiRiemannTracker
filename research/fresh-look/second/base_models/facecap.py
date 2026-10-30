# faces-only lever: does it saturate? compare fixed cap 0.134 vs line-extrapolated cap 0.1+0.06(5143/2000-L)
import slotcost as S
capf = lambda L: 0.1 + 0.06*(5143/2000 - L)
B, h = 0.99999, 0.8097
base = S.theta_star(h, B, 2.0001, capf(2.0001), 2.0)
for c in (1.9, 1.8):
    L = 2.0001*c/2
    a = S.theta_star(h, B, L, capf(2.0001), 2.0); b = S.theta_star(h, B, L, capf(L), 2.0)
    print('Lambda %.3f: fixed cap %+.2e   growing cap(%.3f) %+.2e  (vs bank)' % (L, a-base, capf(L), b-base), flush=True)
