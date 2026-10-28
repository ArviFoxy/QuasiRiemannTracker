"""
e34_vanishing_pools.py -- items 3 and 4 of the task.

PART A  local vanishing table of the prime-power Gauss sum:  Z(j,v) = [ g(p^j, p^v h0) != 0 ]   (h0 prime to p)
        theory (Lean: actualSextic_primePowerGauss_at_pow + sexticGauss_prime_power):
            6 !| j :  nonzero  <=>  v = j-1             (|g| = N^{j-1/2})
            6  | j :  nonzero  <=>  v >= j-1            (g = -N^{j-1} for v = j-1,  phi(p^j) = N^{j-1}(N-1) for v >= j)

PART B  the dilation identity    g(n, D^s h) = chi_n(D)^{[-s]} g(n,h)     (chi^6 := coprimality mask)
        for ALL n (also n not prime to D), ALL h.  Holds for every h  iff  for every p | gcd(D,n):  6 !| v_p(n) and v_p(n) <= s v_p(D).

PART C  pools:  g(u, p^k h) for u = p^i u', i = 0..6 :
            i = 0           : chi_u(p)^{-k} g(u,h)
            i >= 1          : cross(p^i,u') g(p^i, p^k h) chi_{u'}(p)^{-k} g(u',h),  cross = eps(p,u')^i chi_{u'}(p)^{2i}
"""
import time, collections, itertools
from common import *

rng = random.Random(777)
t0 = time.time()

# ---------------------------------------------------------------------------------------------------------
# PART A
# ---------------------------------------------------------------------------------------------------------
print("PART A: local vanishing pattern  Z(j,v)")
cases = [(pick, jmax) for pick, jmax in [(7, 7), (13, 5), (25, 4), (19, 4)]]
A_ok = Counter2()
Zobs = {}
for N, jmax in cases:
    ps = [p for p in PRIMES if norm(p) == N]
    p = ps[0]
    for j in range(1, jmax + 1):
        s = pw(p, j)
        for v in range(0, j + 4):
            h0 = rand_h0(rng, [p])
            H = mul(pw(p, v), h0)
            g = gauss(s, H)
            nz = abs(g) > 1e-6 * math.sqrt(norm(s))
            if j % 6:
                pred = (v == j - 1)
                mag_pred = N ** (j - 0.5)
            else:
                pred = (v >= j - 1)
                mag_pred = None
            A_ok.add(('Z', N), nz == pred, (N, j, v, abs(g)))
            if nz and mag_pred is not None:
                A_ok.add(('mag', N), abs(abs(g) - mag_pred) < 1e-6 * mag_pred, (N, j, v, abs(g)))
            if j % 6 == 0 and nz:
                exp_val = -(N ** (j - 1)) if v == j - 1 else N ** (j - 1) * (N - 1)
                A_ok.add(('ram', N), abs(g - exp_val) < 1e-6 * abs(exp_val), (N, j, v, g))
        Zobs[(N, j)] = [v for v in range(0, j + 4) if abs(gauss(s, mul(pw(p, v), rand_h0(rng, [p])))) > 1e-6 * math.sqrt(norm(s))]
print("  failures:", dict(A_ok.bad), " | checks:", {k: A_ok.ok[k] + A_ok.bad[k] for k in set(A_ok.ok) | set(A_ok.bad)})
print("  observed v with g(p^j, p^v h0) != 0 (norm-7 prime):", {j: Zobs[(7, j)] for j in range(1, 8)})

# the same with an extra coprime factor q (CRT independence) -- n = p^j q
print("  with extra coprime prime factor q (n = p^j q):")
B_ok = Counter2()
for N, jmax in [(7, 4), (13, 3)]:
    p = [x for x in PRIMES if norm(x) == N][0]
    for qN in (13, 19, 31):
        q = [x for x in PRIMES if norm(x) == qN and x != p][0]
        for j in range(1, jmax + 1):
            n = mul(pw(p, j), q)
            if norm(n) > MAXMOD:
                continue
            for v in range(0, j + 3):
                h0 = rand_h0(rng, [p, q])
                H = mul(pw(p, v), h0)
                g = gauss(n, H)
                nz = abs(g) > 1e-6 * math.sqrt(norm(n))
                B_ok.add('Zq', nz == (v == j - 1), (N, qN, j, v))
print("   failures", dict(B_ok.bad), "checks", sum(B_ok.ok.values()) + sum(B_ok.bad.values()))

# ---------------------------------------------------------------------------------------------------------
# PART B
# ---------------------------------------------------------------------------------------------------------
print("\nPART B: dilation identity for non-coprime n")


def lhs_rhs(n, D, s, h):
    """LHS = chi_n(D)^{[-s]} g(n,h)  (0 if D not coprime to n; chi^6 = 1 on coprime);  RHS = g(n, D^s h)"""
    c = chi_exp(D, n)
    if c is None:
        L = 0
    else:
        e = (-s) % 6
        L = zeta6(e * c) * gauss(n, h)
    R = gauss(n, mul(pw(D, s), h))
    return L, R


def criterion(n, D, s):
    """predicted: identity holds for every h"""
    fn = dict(factor(n))
    fD = dict(factor(D))
    for p, vD in fD.items():
        if p in fn:
            j = fn[p]
            if j % 6 == 0 or j > s * vD:
                return False
    return True


tab = collections.defaultdict(lambda: [0, 0])      # (class) -> [holds, total]
viol = Counter2()
for trial in range(1500):
    p = rng.choice([x for x in PRIMES if norm(x) in (7, 13, 25)])
    jmax = {7: 5, 13: 4, 25: 3}[norm(p)]
    j = rng.randint(0, jmax)
    # D: p, p^2, p*q'
    mD = rng.choice([1, 1, 2])
    qprime = rng.choice([x for x in PRIMES if norm(x) in (19, 31, 37) and x != p])
    Dkind = rng.choice(['p', 'p^2', 'pq'])
    D = {'p': p, 'p^2': pw(p, 2), 'pq': mul(p, qprime)}[Dkind]
    # n : p^j times optional coprime prime
    extra = rng.choice([ONE, ONE, rng.choice([x for x in PRIMES if norm(x) in (13, 19, 31) and x != p and x != qprime])])
    n = mul(pw(p, j), extra)
    if n == ONE or norm(n) > 400_000:
        continue
    s = rng.randint(0, 12)
    # frequencies of various valuations at p
    nfac = [x for x, _ in factor(n)]
    ok_all = True
    for t in rng.sample(range(0, 9), 4):
        h = mul(pw(p, t), rand_h0(rng, [p] + nfac + [qprime]))
        L, R = lhs_rhs(n, D, s, h)
        # s = 0 : the identity reads g(n,h) = chi^0 g(n,h) = g(n,h) only for coprime n; we include s>=1 only
        if s == 0:
            continue
        if abs(L - R) > 1e-6 * math.sqrt(norm(n)):
            ok_all = False
    if s == 0:
        continue
    pred = criterion(n, D, s)
    key = ('pred_holds' if pred else 'pred_fails')
    tab[key][1] += 1
    if ok_all:
        tab[key][0] += 1
    if pred and not ok_all:
        viol.add('criterion says holds but a violation was found', False, (n, D, s))
print("  cases where the criterion predicts 'holds for every h':   identity held for all sampled h in %d / %d" % tuple(tab['pred_holds']))
print("  cases where the criterion predicts 'fails for some h':    identity failed for some sampled h in %d / %d" %
      (tab['pred_fails'][1] - tab['pred_fails'][0], tab['pred_fails'][1]))
print("  violations of the sufficiency direction:", dict(viol.bad))

# sharp table (p of norm 7; D = p; vary j and s): fraction of random h for which identity holds
print("  table (p of norm 7, D = p, n = p^j):  'A' identity holds for every sampled h, '.' fails for some h")
p7 = [x for x in PRIMES if norm(x) == 7][0]
print("   s\\j  " + " ".join("%2d" % j for j in range(1, 8)))
for s in range(1, 13):
    row = []
    for j in range(1, 8):
        n = pw(p7, j)
        ok = True
        for t in range(0, j + 3):
            h = mul(pw(p7, t), rand_h0(rng, [p7]))
            L, R = lhs_rhs(n, p7, s, h)
            if abs(L - R) > 1e-6 * math.sqrt(norm(n)):
                ok = False
        row.append(" A" if ok else " .")
        if ok != criterion(n, p7, s):
            viol.add('table', False, (j, s))
    print("   %2d   " % s + " ".join(row))
print("  table violations of the criterion:", dict(viol.bad))

# ---------------------------------------------------------------------------------------------------------
# PART C  pools
# ---------------------------------------------------------------------------------------------------------
print("\nPART C: pool dilations  g(u, p^k h),  u = p^i u'")
C_ok = Counter2()
twist_table = {}
for trial in range(900):
    N = rng.choice([7, 7, 13, 25])
    p = rng.choice([x for x in PRIMES if norm(x) == N])
    imax = {7: 6, 13: 4, 25: 3}[N]
    i = rng.randint(0, imax)
    up = rng.choice([ONE, rng.choice([x for x in PRIMES if norm(x) in (13, 19, 31, 37, 43) and x != p])])
    if rng.random() < 0.4:
        up = mul(up, rng.choice([x for x in PRIMES if norm(x) in (13, 19) and x != p and x != up]))
    if up == ONE and i == 0:
        continue
    u = mul(pw(p, i), up)
    if norm(u) > 700_000:
        continue
    k = rng.randint(0, 12)
    nfac = [x for x, _ in factor(up)]
    # frequency h = p^t * h0, h0 prime to p and to u' (so that g(u',h) is non-zero for squarefree u')
    t = rng.choice([0, 0, 1, 2, 3, 4, 5, 6])
    h = mul(pw(p, t), rand_h0(rng, [p] + nfac))
    H = mul(pw(p, k), h)
    v = k + t
    g_u = gauss(u, H)
    g_up_h = gauss(up, h) if up != ONE else 1.0
    if i == 0:
        c = chi_exp(p, up) if up != ONE else 0
        pred = zeta6(-k * c) * gauss(u, h)
        C_ok.add('i=0 twist chi_u(p)^{-k}', abs(g_u - pred) < 1e-6 * math.sqrt(norm(u)) , (u, k, h))
    else:
        nz_pred = (v == i - 1) if i % 6 else (v >= i - 1)
        nz = abs(g_u) > 1e-6 * math.sqrt(norm(u))
        # nonvanishing of the full thing also requires g(up, h) != 0; only test when generic
        if abs(g_up_h) > 1e-6:
            C_ok.add('vanishing pattern (i>=1)', nz == nz_pred, (i, k, t, abs(g_u)))
            if nz and up != ONE:
                # ratio to  g(p^i, H) g(u', h)
                gpi = gauss(pw(p, i), H)
                rat = g_u / (gpi * g_up_h)
                c = chi_exp(p, up)
                e = (ray_sign_exp(pw(p, i), up) + (2 * i - k) * c) % 6
                C_ok.add('nonvanishing: ratio = eps^i chi^{2i-k}', abs(rat - zeta6(e)) < 1e-6, (i, k, t, rat, e))
                twist_table.setdefault((i, k), 0)
                twist_table[(i, k)] += 1
print("  failures:", dict(C_ok.bad))
print("  checks:", {k: C_ok.ok[k] + C_ok.bad[k] for k in set(C_ok.ok) | set(C_ok.bad)})
print("  (i,k) pairs seen with non-vanishing g(p^i u', p^k h) (t = v_p(h)):", sorted(twist_table.items())[:40])
print("time %.1fs" % (time.time() - t0))
