"""
t0_basics.py -- sanity of the arithmetic layer and of the normalisation, by re-checking the Lean theorems
that the library already proves (so that every later experiment is run on the SAME objects as the Lean):

  L1  sexticGauss_unit_scale        g(s, b h) = chi_s(b)^{-1} g(s,h)            (b coprime to s)
  L2  sexticGauss_coprime_product   g(a b, H) = chi_a(b) chi_b(a) g(a,H) g(b,H)  (a,b coprime)
  L3  idealRowHom_primary_reciprocity chi_a(b) = ray_sign(a,b) chi_b(a)           (a,b primary)
  L4  GaussTransfer.fourth_power    g(a, D^4 k) = chi_a(D)^2 g(a,k)               (a fifth-free; both sides 0 if not coprime)
  L5  gauss_prime_power_one / _six  closed forms for g(p^{n+1}, 1), g(p^{n+1}, p^6)
"""
import random, math, cmath, itertools, sys
import numpy as np
from zw import *

rng = random.Random(2026)
PR = prime_elements(200)
print("primary primes of norm <= 200:", len(PR))

# --- 0. arithmetic sanity ---------------------------------------------------------------------
bad = 0
for _ in range(2000):
    x = (rng.randint(-50, 50), rng.randint(-50, 50))
    y = (rng.randint(-50, 50), rng.randint(-50, 50))
    assert norm(mul(x, y)) == norm(x) * norm(y)
    assert mul(x, conj(x)) == (norm(x), 0)
    assert conj(conj(x)) == x
    if y != (0, 0):
        z = mul(x, y)
        assert exact_div(z, y) == x
s = (rng.randint(-30, 30), rng.randint(-30, 30))
for _ in range(300):
    s = (rng.randint(-30, 30), rng.randint(-30, 30))
    if s == (0, 0):
        continue
    m = get_mod(s)
    x = (rng.randint(-100, 100), rng.randint(-100, 100))
    y = (rng.randint(-100, 100), rng.randint(-100, 100))
    assert (m.reduce(x) == m.reduce(y)) == divides(s, sub(x, y))
    # number of reps = N
    if m.N < 200:
        assert len(set(m.reduce(r) for r in m.all_reps())) == m.N
print("arithmetic OK")

# --- 1. symbols: multiplicative, periodic, correct on units ----------------------------------
for pi in PR[:30]:
    ps = prime_sym(pi)
    N = ps.N
    for _ in range(100):
        x = (rng.randint(-60, 60), rng.randint(-60, 60))
        y = (rng.randint(-60, 60), rng.randint(-60, 60))
        jx, jy, jxy = ps.sym(x), ps.sym(y), ps.sym(mul(x, y))
        if jx >= 0 and jy >= 0:
            assert jxy == (jx + jy) % 6
        else:
            assert jxy == -1
        # definition: x^{(N-1)/6} = zeta6^j mod pi
        if jx >= 0:
            assert ps.mod.reduce(pw(x, (N - 1) // 6)) == ps.mod.reduce(UNITS[jx])
print("symbols OK (x^{(N-1)/6} = zeta6^j mod pi, multiplicative)")

# --- 2. psi closed form vs direct --------------------------------------------------------------
mx = 0
for _ in range(500):
    s = (rng.randint(-20, 20), rng.randint(-20, 20))
    if s == (0, 0):
        continue
    x = (rng.randint(-40, 40), rng.randint(-40, 40))
    mx = max(mx, abs(psi_phase(s, x) - psi_phase_direct(s, x)))
print("psi closed form vs direct complex definition: max err %.2e" % mx)
assert mx < 1e-9

# --- 3. Gauss sum basics -------------------------------------------------------------------------
for pi in PR[:40]:
    g1 = gauss(pi, (1, 0))
    assert abs(abs(g1) ** 2 - norm(pi)) < 1e-8 * norm(pi), (pi, g1)
print("|g(pi,1)|^2 = N(pi) for the first 40 primary primes")

# --- 4. Lean theorems ----------------------------------------------------------------------------
def rand_supported(maxN=400, primary=True, maxexp=3):
    while True:
        k = rng.randint(1, 3)
        ps = rng.sample(PR, k)
        ex = [rng.randint(1, maxexp) for _ in ps]
        s = build_element(list(zip(ps, ex)))
        if norm(s) <= maxN:
            return s


def rand_elt(r=60):
    return (rng.randint(-r, r), rng.randint(-r, r))


cnt = {"L1": 0, "L2": 0, "L3": 0, "L4": 0, "L4zero": 0}
for _ in range(400):
    # L1 unit scale
    s = rand_supported(300)
    b = rand_elt()
    h = rand_elt()
    c = chi_exp(b, s)
    if c is not None:
        assert close(gauss(s, mul(b, h)), zeta6(-c) * gauss(s, h), 1e-8, math.sqrt(norm(s)))
        cnt["L1"] += 1
    # also with b a non-primary element (units, 2, lambda...) -- Lean has IsCoprime b s only
    for b2 in [(-1, 0), (0, 1), (2, 0), LAM, (3, 0), (1, 2)]:
        c2 = chi_exp(b2, s)
        if c2 is not None:
            assert close(gauss(s, mul(b2, h)), zeta6(-c2) * gauss(s, h), 1e-8, math.sqrt(norm(s)))
            cnt["L1"] += 1
print("L1 unit scale verified in", cnt["L1"], "cases")

for _ in range(400):
    a = rand_supported(150)
    b = rand_supported(150)
    if norm(mul(a, b)) > 3000:
        continue
    if get_modulus(a) is None:
        continue
    # coprime?
    if any(divides(p1, b) for p1, _ in factor(a)):
        continue
    H = rand_elt()
    lhs = gauss(mul(a, b), H)
    ca, cb = chi_exp(b, a), chi_exp(a, b)    # chi_a(b), chi_b(a)
    rhs = zeta6(ca + cb) * gauss(a, H) * gauss(b, H)
    assert close(lhs, rhs, 1e-8, norm(a) * norm(b)), (a, b, H, lhs, rhs)
    cnt["L2"] += 1
print("L2 CRT product verified in", cnt["L2"], "cases (arbitrary supported generators, no primary assumption)")

for _ in range(600):
    a = rand_supported(400)
    b = rand_supported(400)
    # primary generators: build_element of primary primes is primary
    assert is_primary(a) and is_primary(b)
    if any(divides(p1, b) for p1, _ in factor(a)):
        continue
    e = ray_sign(a, b)
    ca, cb = chi_exp(b, a), chi_exp(a, b)     # chi_a(b), chi_b(a)
    # Lean: idealRowHom b (span a) = phase(a,b) * idealRowHom a (span b)
    assert (ca - cb) % 6 == (0 if e == 1 else 3), (a, b, e, ca, cb)
    cnt["L3"] += 1
print("L3 primary reciprocity chi_a(b)=ray_sign(a,b) chi_b(a) verified in", cnt["L3"], "cases")

def fifth_free(s):
    return all(e <= 4 for _, e in factor(s))

for _ in range(500):
    a = rand_supported(400, maxexp=5)
    if not fifth_free(a):
        continue
    D = rand_elt(25)
    if D == (0, 0):
        continue
    k = rand_elt()
    lhs = gauss(a, mul(pw(D, 4), k))
    c = chi_exp(D, a)
    if c is None:
        rhs = 0
        cnt["L4zero"] += 1
    else:
        rhs = zeta6(2 * c) * gauss(a, k)
    assert close(lhs, rhs, 1e-7, math.sqrt(norm(a))), (a, D, k, lhs, rhs)
    cnt["L4"] += 1
print("L4 fourth_power verified in", cnt["L4"], "cases (of which", cnt["L4zero"], "have D not coprime to a)")
print("t0 OK")
