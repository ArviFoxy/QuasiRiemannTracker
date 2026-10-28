"""
e12_cross_dilation.py -- items 1 and 2 of the task.

For a block B = D^m (D prime, primary; m = 1..6) and a residual n (primary, coprime to D) with a frequency h for which
all the local Gauss sums are non-zero (v_p(h) = j_p - 1 at every prime power p^{j_p} || B n), we measure

    cross(B,n,h)   := g(B n, h) / ( g(B,h) g(n,h) )                       (CRT cross factor)
    leftover(m,k)  := g(B n, h) / ( g(B,h) g(n, D^k h) )                  (what is left after dilating the residual by D^k)

and compare with the prediction  (Lean: crossFactor_primary / normalized_coprime_product + unit scale)

    cross    = eps(D,n)^m * chi_n(D)^{2m}          eps = quadraticRaySign (the ray sign, +-1, depends on D,n mod 4)
    leftover = eps(D,n)^m * chi_n(D)^{2m+k}        (because g(n, D^k h) = chi_n(D)^{-k} g(n,h))

All exponents are exact integers mod 6; the Gauss sums are double precision (tolerance 1e-7 on the ratio).
Extra outputs: negative controls for the statement "(b) D^1 leaves (D/n)_2", coverage of the 144 class pairs mod 4,
and the free-variable form (frequency h = D^{m-1} H', residual evaluated at D^{(5-m) mod 6} H').
"""
import sys, time, collections
from common import *

SEED = int(sys.argv[1]) if len(sys.argv) > 1 else 20261028
SCALE = float(sys.argv[2]) if len(sys.argv) > 2 else 1.0
rng = random.Random(SEED)
t0 = time.time()

DS = [(7, 'split'), (13, 'split'), (19, 'split'), (31, 'split'), (37, 'split'), (43, 'split'), (61, 'split'), (25, 'inert'), (121, 'inert')]
Dprimes = {}
for p in PRIMES:
    Dprimes.setdefault(norm(p), []).append(p)


def pick_D(N):
    return rng.choice(Dprimes[N])


def pick_n(D, limit, rng):
    """random primary n coprime to D with 2 <= N(n) <= limit; exponent patterns 1, 11, 2, 12"""
    for _ in range(1000):
        npr = rng.choice([1, 1, 1, 2, 2])
        cand = [p for p in PRIMES if p != D and norm(p) <= limit]
        if not cand:
            return None
        ps = rng.sample(cand, min(npr, len(cand)))
        ex = [rng.choice([1, 1, 1, 2]) for _ in ps]
        n = build_element(list(zip(ps, ex)))
        if 1 < norm(n) <= limit:
            return n, dict(zip(ps, ex))
    return None


cnt = Counter2()
table = {}                       # (m,k) -> [passed, total]
cross_counts = {}                # m -> [passed,total]
mag_ok = Counter2()
cubic_recip = Counter2()
coverage = set()
neg = collections.Counter()
kappa = Counter2()
kappa_tab = {}

CASES = {1: 500, 2: 450, 3: 350, 4: 200, 5: 60, 6: 25}
CAP = {1: 400_000, 2: 400_000, 3: 600_000, 4: 1_000_000, 5: 1_800_000, 6: 1_800_000}

for m in range(1, 7):
    ncases = int(CASES[m] * SCALE)
    done = 0
    while done < ncases:
        allowed = [N for N, _ in DS if N ** m * 7 <= CAP[m]]
        N = rng.choice(allowed)
        D = pick_D(N)
        B = pw(D, m)
        limit = max(2, CAP[m] // (N ** m))
        pn = pick_n(D, min(limit, 150), rng)
        if pn is None:
            continue
        n, nf = pn
        fe = merge({D: m}, nf)
        h = generic_h(rng, fe)
        s = mul(B, n)
        gB, gn, gs = gauss(B, h), gauss(n, h), gauss(s, h)
        expect = N ** (m - 0.5) if m % 6 else N ** (m - 1)
        mag_ok.add(m, abs(abs(gB) - expect) < 1e-6 * expect, (D, m, h, gB))
        if abs(gB) < 1e-6 or abs(gn) < 1e-6:
            continue
        done += 1
        cobs = root_index(gs / (gB * gn))
        c = chi_exp(D, n)                 # chi_n(D) exponent (D coprime to n)
        e_sign = ray_sign_exp(B, n)       # eps(B,n) = eps(D,n)^m
        assert ray_sign(B, n) == ray_sign(D, n) ** m
        cpred = (e_sign + 2 * m * c) % 6
        cross_counts.setdefault(m, [0, 0])
        cross_counts[m][1] += 1
        if cobs == cpred:
            cross_counts[m][0] += 1
        else:
            cnt.add(('cross', m), False, (D, m, n, h, cobs, cpred))
        if m % 2 == 1:
            coverage.add(((D[0] % 4, D[1] % 4), (n[0] % 4, n[1] % 4)) if m == 1 else None)
        c_rev = chi_exp(n, D)
        cubic_recip.add(m, (2 * c - 2 * c_rev) % 6 == 0 and ((3 * c - 3 * c_rev) % 6 == (0 if ray_sign(D, n) == 1 else 3)),
                        (D, n, c, c_rev))
        for k in range(0, 13):
            Dk = pw(D, k)
            gk = gauss(n, mul(Dk, h))
            lobs = root_index(gs / (gB * gk))
            lpred = (e_sign + (2 * m + k) * c) % 6
            key = (m, k)
            table.setdefault(key, [0, 0])
            table[key][1] += 1
            if lobs == lpred:
                table[key][0] += 1
            else:
                cnt.add(('left', m, k), False, (D, m, n, h, lobs, lpred))
            if m == 1 and k == 1:
                # negative controls for the claim "D^1 leaves (D/n)_2":
                #   (D/n)_2 := chi_n(D)^3  (symbol of D modulo n),   (n/D)_2 := chi_D(n)^3 (symbol of n modulo D)
                Dn = (3 * c) % 6
                nD = (3 * chi_exp(n, D)) % 6
                neg['cases'] += 1
                neg['leftover == (n/D)_2'] += (lobs == nD)
                neg['leftover == (D/n)_2'] += (lobs == Dn)
                neg['eps == -1'] += (ray_sign(D, n) == -1)
                neg['leftover != (D/n)_2 (needs eps=-1)'] += (lobs != Dn)
        # free-variable form: h = D^{m-1} H'  ->  g(B n, h) = eps^m chi^{...} g(B,h) g(n, D^{kappa} H'),  kappa = (5-m) mod 6
        if m <= 5:
            Hp = exact_div(h, pw(D, m - 1))
            assert Hp is not None
            kap = (5 - m) % 6
            g_res = gauss(n, mul(pw(D, kap), Hp))
            kappa.add(m, root_index(gs / (gB * g_res)) == e_sign % 6, (D, m, n, h))
            # full kappa table: leftover'(m, kappa) = eps^m chi_n(D)^{m+kappa+1}
            for kp in range(0, 7):
                g_r = gauss(n, mul(pw(D, kp), Hp))
                kappa_tab.setdefault((m, kp), [0, 0])
                kappa_tab[(m, kp)][1] += 1
                kappa_tab[(m, kp)][0] += (root_index(gs / (gB * g_r)) == (e_sign + (m + kp + 1) * c) % 6)
    print("m=%d done  (%.0fs)" % (m, time.time() - t0), flush=True)

print()
print("=== magnitude |g(D^m,h)| = N^{m-1/2} (m<6), N^{5} (m=6) at v_D(h)=m-1 : failures:", sum(mag_ok.bad.values()),
      "of", sum(mag_ok.ok.values()) + sum(mag_ok.bad.values()))
print("=== cross factor = eps(D,n)^m chi_n(D)^{2m}:")
for m in range(1, 7):
    ok, tot = cross_counts.get(m, [0, 0])
    print("   m=%d : %d / %d cases match" % (m, ok, tot))
print("=== cubic reciprocity chi_n(D)^2 = chi_D(n)^2 and chi_D(n)^3 = eps * chi_n(D)^3 : failures:", sum(cubic_recip.bad.values()),
      " of ", sum(cubic_recip.ok.values()) + sum(cubic_recip.bad.values()))
print("=== class pairs (D mod 4, n mod 4) covered for m=1: %d of 144" % len([c for c in coverage if c]))
print()
print("=== leftover(m,k) = eps^m chi_n(D)^{2m+k}   (passed/total):")
hdr = "m\\k " + " ".join("%7d" % k for k in range(0, 13))
print(hdr)
for m in range(1, 7):
    row = []
    for k in range(0, 13):
        ok, tot = table.get((m, k), [0, 0])
        row.append("%3d/%-3d" % (ok, tot))
    print("m=%d " % m + " ".join(row))
print()
print("=== negative control, m=1,k=1:", dict(neg))
print("=== free-variable form  g(D^m n, D^{m-1}H') = eps^m g(D^m, D^{m-1}H') g(n, D^{(5-m) mod 6} H')  [kappa-view]:")
for m in range(1, 6):
    print("   m=%d : %d / %d" % (m, kappa.ok[m], kappa.ok[m] + kappa.bad[m]))
print("=== free-variable leftover table  leftover'(m,kappa) = eps^m chi_n(D)^{m+kappa+1}  (passed/total), kappa = 0..6:")
for m in range(1, 6):
    print("   m=%d : " % m + " ".join("%d/%d" % tuple(kappa_tab[(m, kp)]) for kp in range(0, 7)))
print()
print("failures:", dict(cnt.bad))
if cnt.examples:
    for k, v in cnt.examples.items():
        print("  example", k, v)
print("time %.1fs" % (time.time() - t0))
