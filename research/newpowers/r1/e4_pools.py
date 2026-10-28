"""
e4_pools.py -- item 4 of the task (systematic grid).

For a pool prime p, a column u = p^i u' (p !| u', u' squarefree and prime to the frequency's other primes) and a
frequency H = p^k h  (h prime to p; v_p(h) = t = 0 in the main grid, t = 1,2 in the second grid):

   i = 0 :   g(u, p^k h) = chi_u(p)^{-k} g(u, h)                                   (unit scale, Lean sexticGauss_unit_scale)
   i >= 1:   g(u, p^k h) = 0 unless  v_p(p^k h) = k + t = i - 1   (6 !| i)    or  k + t >= i - 1 (6 | i);
             if non-zero:   g(u,H) / ( g(p^i,H) g(u',h) ) = eps(p,u')^i chi_{u'}(p)^{2i-k}
We tabulate, for every (i,k), whether the column survives and its twist relative to the surviving local Gauss sum.
"""
import collections, time
from common import *

rng = random.Random(4242)
t0 = time.time()
ok = Counter2()
surv = collections.defaultdict(lambda: [0, 0])           # (i,k,t) -> [nonzero observed, tested]
twist_free = collections.defaultdict(lambda: [0, 0])      # (i,k,t) -> [ratio==1 count, nonzero count]
twist_sign_only = collections.defaultdict(lambda: [0, 0])

SPECS = [(7, 7), (13, 4), (25, 3)]       # (norm of p, max i)
for t in (0, 1, 2):
    for N, imax in SPECS:
        for i in range(0, imax + 1):
            for k in range(0, 13):
                for rep in range(3):
                    p = rng.choice([x for x in PRIMES if norm(x) == N])
                    # residual u' : 1 or one/two primes
                    pool = [x for x in PRIMES if norm(x) in (13, 19, 31, 37, 43) and x != p]
                    up = ONE if rep == 0 else (rng.choice(pool) if rep == 1 else mul(rng.choice(pool[:6]), rng.choice(pool[6:])))
                    if i == 0 and up == ONE:
                        continue
                    u = mul(pw(p, i), up)
                    if norm(u) > 900_000:
                        continue
                    nfac = [x for x, _ in factor(up)] if up != ONE else []
                    h = mul(pw(p, t), rand_h0(rng, [p] + nfac))
                    H = mul(pw(p, k), h)
                    g_u = gauss(u, H)
                    if i == 0:
                        c = chi_exp(p, up)
                        pred = zeta6(-k * c) * gauss(u, h)      # h already contains the factor p^t
                        ok.add('i=0: g(u,p^k h) = chi_u(p)^{-k} g(u,h)', abs(g_u - pred) < 1e-6 * math.sqrt(norm(u)), (u, k, t))
                        continue
                    v = k + t
                    pred_nz = (v == i - 1) if i % 6 else (v >= i - 1)
                    nz = abs(g_u) > 1e-6 * math.sqrt(norm(u))
                    gup = gauss(up, h) if up != ONE else 1.0
                    if abs(gup) < 1e-6:
                        continue
                    ok.add('vanishing pattern', nz == pred_nz, (N, i, k, t, abs(g_u)))
                    surv[(i, k, t)][1] += 1
                    if nz:
                        surv[(i, k, t)][0] += 1
                        gpi = gauss(pw(p, i), H)
                        rat = g_u / (gpi * gup)
                        c = chi_exp(p, up) if up != ONE else 0
                        e = (ray_sign_exp(pw(p, i), up) + (2 * i - k) * c) % 6 if up != ONE else 0
                        ok.add('ratio = eps^i chi^{2i-k}', abs(rat - zeta6(e)) < 1e-6, (N, i, k, t, rat, e))
                        if up != ONE:
                            twist_free[(i, k, t)][1] += 1
                            if e == 0:
                                twist_free[(i, k, t)][0] += 1

print("failures:", dict(ok.bad))
print("checks:", {k: ok.ok[k] + ok.bad[k] for k in set(ok.ok) | set(ok.bad)})
print()
print("surviving (i,k) at t = v_p(h) = 0   [i = v_p(u), k = dilation exponent]  (nonzero cases / tested):")
for i in range(1, 8):
    row = []
    for k in range(0, 13):
        a = surv.get((i, k, 0))
        row.append(("%d/%d" % tuple(a)) if a else " -  ")
    print("  i=%d : " % i + " ".join("%5s" % r for r in row))
print("   (k = 0..12 left to right)")
print()
print("twist of the surviving class relative to g(p^i,H) g(u',h):  eps(p,u')^i chi_{u'}(p)^{2i-k};   i = k+1+t:")
for (i, k, t), (a, b) in sorted(surv.items()):
    if a and t == 0 and i <= 6 and k == i - 1:
        e_chi = (2 * i - k) % 6
        print("   i=%d k=%d : chi exponent 2i-k = %d  (mod 6) -> %s ; eps^%d" %
              (i, k, e_chi, {0: 'trivial', 3: 'quadratic', 2: 'cubic', 4: 'cubic', 1: 'sextic', 5: 'sextic'}[e_chi], i))
print("time %.1fs" % (time.time() - t0))
