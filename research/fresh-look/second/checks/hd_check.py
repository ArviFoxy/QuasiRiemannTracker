# Check g(chi) g(chi^4) = conj(chi(4)) g(chi^2) g(chi^3) for sextic chi on F_p, p = 1 mod 6,
# and J(chi,chi) = conj(chi(4)) J(chi, eta) for all nontrivial chi.
import cmath
def prim_root(p):
    for g in range(2, p):
        if all(pow(g, (p-1)//q, p) != 1 for q in set(f for f in range(2, p) if (p-1) % f == 0 and all(f % d for d in range(2, int(f**0.5)+1)))):
            return g
def run(p):
    g = prim_root(p); ind = {}; x = 1
    for k in range(p-1): ind[x] = k; x = x*g % p
    e = lambda a: cmath.exp(2j*cmath.pi*a/p)
    def chi(j, a):  # character of order dividing (p-1), chi(g) = exp(2 pi i j/(p-1))
        a %= p
        return 0 if a == 0 else cmath.exp(2j*cmath.pi*j*ind[a]/(p-1))
    G = lambda j: sum(chi(j, a)*e(a) for a in range(1, p))
    J = lambda j1, j2: sum(chi(j1, a)*chi(j2, 1-a) for a in range(p))
    s = (p-1)//6; h = (p-1)//2
    lhs = G(s)*G(4*s); rhs = chi(s, 4).conjugate()*G(2*s)*G(3*s)
    worst = max(abs(J(j, j) - chi(j, 4).conjugate()*J(j, h)) for j in range(1, p-1))
    return abs(lhs-rhs), worst
for p in (7, 13, 19, 31, 37, 43, 61, 67, 73, 79, 97, 103, 109):
    print(p, '%.2e %.2e' % run(p))
