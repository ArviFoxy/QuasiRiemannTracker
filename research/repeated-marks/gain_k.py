"""Exact HIGH gain with k copies of the marks in the inverse witness (Lemma 8.1), natural plain face.
f_p(S,F) = (1-2p) nu S + nu (xi_p - xi0 F);  G_k = min_p f_p.
Facets at p=1/2 (k copies):  (2k+1) phi S/3,  k A S + B F,  nu w/(10+3w) S + 2 nu w^2/(t(10+3w)) F,  C F."""
import numpy as np


def xi_p(nu, S, F, p, k, al=5/6, plain='nat', BL=None):
    kk = al - nu
    q1 = 1 - p
    inv = [(1/q1, p*F/q1)]                       # inverse cap: r >= (xi - pF)/(1-p)
    if k is not None:
        inv.append((1.0, 2*p*k*S))               # k copies of the marks: r >= xi - 2pkS
    if plain == 'nat':
        pl = [(1.0, 2*p*S), (9/(9-4*p), 4*p*F/(9-4*p))]
    else:  # earlier affine face (B, Lam, hcap): z_P = min(S, h F, (B F - y)/Lam)
        B, Lam, hc = BL
        pl = [(1.0, 2*p*S), (1.0, 2*p*hc*F)]
        pl.append((1/(1-2*p/Lam), (2*p*B*F/Lam)/(1-2*p/Lam)))
    roots = []
    for (ai, bi) in inv:
        for (aj, bj) in pl:
            den = nu + kk*(ai + aj/2)
            roots.append((al*F + kk*(bi + bj/2))/den)
    return np.minimum.reduce(roots)


def f_p(nu, S, F, p, k, **kw):
    al = kw.get('al', 5/6)
    xi0F = al*F/(nu + 1.5*(al-nu))
    return (1-2*p)*nu*S + nu*(xi_p(nu, S, F, p, k, **kw) - xi0F)


def G(nu, S, F, k, ps=np.linspace(0, 0.5, 201), **kw):
    vals = np.array([f_p(nu, S, F, p, k, **kw) for p in ps])
    i = np.argmin(vals, axis=0)
    return vals.min(axis=0), ps[i]


def facets_half(nu, S, F, k):
    w = 5-6*nu; d = 5-2*nu; t = 3*d
    phi = nu*w/d; A = 14*nu*w/(115-54*nu); B = 2*nu*w*w/(3*d*(115-54*nu)); C = 16*nu*w*w/(3*d*(185-138*nu))
    return np.minimum.reduce([(2*k+1)*phi*S/3, k*A*S+B*F,
                              nu*w/(10+3*w)*S + 2*nu*w*w/(t*(10+3*w))*F, C*F])


if __name__ == "__main__":
    nus = np.linspace(0.5, 0.75, 26)
    for k in (1, 2, 3):
        bad = []
        for x in np.linspace(0.001, 0.3, 300):
            g, pa = G(nus, x, 1.0, k)
            fh = facets_half(nus, x, 1.0, k)
            dif = fh - g
            if dif.max() > 1e-12:
                j = np.argmax(dif)
                bad.append((round(x, 4), round(nus[j], 3), dif[j], pa[j]))
        print(f"k={k}: points where some p<1/2 is strictly worse than p=1/2: {len(bad)}")
        if bad:
            print("   first few:", bad[:4], " max gap", max(b[2] for b in bad))
