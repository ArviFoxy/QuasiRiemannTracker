# Rigorous-shape adversary: beta' = g~ on every composite column; on prime columns pi (N(pi) > N/7, hence
# dividing no composite column) choose beta'(pi) in lam(pi)^(1/3)*{1,w,w^2} (so beta'^3 = lam, |beta'|=1 and
# twisted multiplicativity all hold) to align c' = beta'*A with (i) one character chi_k0, (ii) a spread
# direction F = sum_k eps_k chi_k / sqrt(K').  Report ||Phi c'||^2/Diag and coherence statistics.
# usage: python3 exp_prime_adversary.py K N [L]
import sys, os, math, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from build import load
W3 = np.exp(2j * np.pi / 3)
K, N = int(sys.argv[1]), int(sys.argv[2]); L = int(sys.argv[3]) if len(sys.argv) > 3 else 60
d = load(K, N, L, os.path.join(os.path.dirname(os.path.abspath(__file__)), 'data'))
Phi = d['Phi'].astype(float); gt = d['gt']; lam = d['lam']; Xe = d['Xe']; markN = d['markN']
colps = d['colps']
Kp, Np = Phi.shape
isprime = np.array([s.count(',') == 0 for s in colps])
X = np.where(Xe < 0, 0, W3 ** np.where(Xe < 0, 0, Xe))
for name, Am in [('unmarked (A=1)', np.ones(Np)), ('marked, A=sum_P q^-1/2 conj((n/P)_3)', (X.conj() / np.sqrt(markN)).sum(1))]:
    c = gt * Am
    diag = np.sum((Phi ** 2) @ np.abs(c) ** 2)
    def rep(cv, lab):
        v = Phi @ cv
        S = np.sum(np.abs(v) ** 2)
        coh = np.abs(v) ** 2 / Np
        print(f'   {lab:44s} ratio={S/diag:7.3f}  max_k|S_k|^2/N\'={coh.max():8.2f}  median={np.median(coh):6.2f}')
    print(f'{name}: K\'={Kp} N\'={Np} prime columns {isprime.mean():.1%}; allowance {(Kp+Np)*np.sum(np.abs(c)**2)/diag:.1f}')
    rep(c, 'true beta = g~')
    l13 = np.exp(1j * np.angle(lam) / 3)
    cands = l13[:, None] * W3 ** np.arange(3)[None, :]          # N' x 3
    def align(target):
        # choose beta'(pi) on primes to maximize Re( beta' A conj(target) ) given the composite part phase
        base = np.vdot(target, np.where(isprime, 0, c))       # current correlation from composites
        ph = base / abs(base) if abs(base) > 0 else 1
        score = np.real(cands * (Am * np.conj(target) * np.conj(ph))[:, None])
        best = cands[np.arange(Np), np.argmax(score, 1)]
        return np.where(isprime, best * Am, c)
    rep(align(Phi[Kp // 2]), "aligned to one chi_k0 (primes only)")
    rng = np.random.default_rng(3)
    F = (rng.choice([-1, 1], Kp) @ Phi) / math.sqrt(Kp)
    rep(align(F), "aligned to spread F (primes only)")
