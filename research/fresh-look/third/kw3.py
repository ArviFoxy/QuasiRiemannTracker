# Restricted-width continuation of the native line below Lambda=2: start at the banked K=1/2 end face (unrestricted),
# then K<1/2 steps whose faces are claimed only for slot widths S >= s0. Parent price: restricted parent if the
# retained width s >= s0, else the unrestricted base face (0.99999, 2.0001, 0.1343). Selected norm with excess gamma.
import sys, time, numpy as np
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/selected-leaf')
import root_ledger as R
from kw import e_sel_vec
BASE = (0.99999, 2.0001, 0.134284)
def run_from_base(K, s0, B=0.99999, h=1e-5, c6=6.0):
    L, c = BASE[1], BASE[2]; path = [(L, c, 0.0)]
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
def worst(B, L, c, a, L0, c0, delta, gamma, s0, nS=81, nt=9):
    wv, where = -1e9, None
    for S in np.linspace(0.0, c, nS)[1:]:
        if S < s0: continue
        w = S; u = a*w; PCmax = B - L*S
        for PC in np.linspace(0.5*PCmax, PCmax, 6):
            for s in (w - u, 0.9*(w-u), 0.75*(w - u), 0.5*(w - u), 0.25*(w-u), 0.1*(w-u)):
                for t in np.linspace(0.0, 1 + 6*u, nt):
                    M = 1 + t - 6*u
                    for frac in (0.5, 0.4, 0.3, 0.0):
                        x1, x2 = PC*(1 - frac), PC*frac
                        sel = e_sel_vec(x1, x2, s, M, delta, gamma) - M
                        if s >= s0: par = R.deletion_need(B, L0, c0, PC, s, M)
                        else: par = R.deletion_need(BASE[0], BASE[1], BASE[2], PC, s, M)
                        v = min(sel, par) - u
                        if v > wv: wv, where = v, (round(S,4), round(s,4), round(M,4), round(sel,5), round(par,6), u)
    return wv, where
K = float(sys.argv[1]); gammas = [float(g) for g in sys.argv[2].split(',')]; s0s = [float(x) for x in sys.argv[3].split(',')]
for s0 in s0s:
    Lend, cend, reason, path = run_from_base(K, s0)
    print('K=%.4f s0=%.3f: restricted line from 2.0001 ends L=%.5f cap %.4f (%s), %d steps' % (K, s0, Lend, cend, reason, len(path)), flush=True)
    idx = sorted(set([1, len(path)//4, len(path)//2, 3*len(path)//4, len(path)-1]))
    for g in gammas:
        res = []
        for i in idx:
            L, c, a = path[i]; L0, c0, _ = path[i-1]
            v, wh = worst(0.99999, L, c, a, L0, c0, K, g, s0)
            res.append('L=%.4f:%s' % (L, 'ok' if v <= 0 else 'FAIL(%+.1e S=%.3f s=%.3f)' % (v, wh[0], wh[1])))
        print('   gamma=%.3f  ' % g + '  '.join(res), flush=True)
