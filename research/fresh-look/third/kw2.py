# K-wall ledger along the native line with the prime-dilated reference; child faces restricted to S >= s0.
import sys, time, numpy as np
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/selected-leaf')
import root_ledger as R
from kw import worst
def run_pd(K, B=0.99999, L0=3.72, c0=0.06, h=1e-5, c6=6.0):
    L, c = L0, c0; path = [(L, c, 0.0)]
    while True:
        Ln = L - h; den = L*(1 + K) - c6*K*B
        if den <= 0: return L, c, 'overshoot', path
        a = K*h/den*(1 + 1e-9)
        if a > (Ln - 1)/(c6 - 2): return L, c, 'selected branch', path
        cn = c/(1 - a + c6*a*c)*(1 - 1e-12); S = cn
        g = min((1 + S)/2, 3/4 - S, (6 + S)/11)
        ok = {'principal': (3/4 + g/2 - B) + (Ln - 2)*S - 4.5*a*S > 0, 'diagonal': Ln - 1 - 4*a > 0,
              'secondRef': 1.5*Ln - 2.5 - 4.5*a > 0, 'refPos': 1/6 - (1 + 1.5*a)*cn > 0, 'H': 1 - c6*a*cn > 0, 'cap_lt': c < 1/6}
        bad = [k for k, v in ok.items() if not v]
        if bad: return L, c, ','.join(bad), path
        L, c = Ln, cn; path.append((L, c, a))
K = float(sys.argv[1]); gammas = [float(g) for g in sys.argv[2].split(',')]; s0s = [float(x) for x in sys.argv[3].split(',')]
Lend, cend, reason, path = run_pd(K)
print('K=%.4f line (pd reference) ends L=%.5f cap %.4f (%s), %d steps' % (K, Lend, cend, reason, len(path)), flush=True)
t0 = time.time()
for Lq in [float(x) for x in sys.argv[4].split(',')] + [Lend + 3e-5]:
    i = min(range(1, len(path)), key=lambda j: abs(path[j][0] - Lq)); L, c, a = path[i]; L0, c0, _ = path[i-1]
    print(' L=%.5f cap=%.4f a=%.3e' % (L, c, a), flush=True)
    for g in gammas:
        row = []
        for s0 in s0s:
            v, wh = worst(0.99999, L, c, a, 0.99999, L0, c0, K, g, s0, nS=81, nt=9)
            row.append('S>=%.3f: %s' % (s0, ('PASS %.1e' % v) if v <= 0 else ('fail %+.2e@S=%.4f' % (v, wh[0]))))
        print('   gamma=%.3f  ' % g + ' | '.join(row) + '  [%.0fs]' % (time.time()-t0), flush=True)
