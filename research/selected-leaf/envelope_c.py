"""Native line with packed-envelope coefficient c (H = 1 + t - c u; Sil's c = 6 = 2 + 4 from the D^4 transfer),
K = 1/2 + eta (PR 93's selected norm), principal gate from ReferenceAt_gamma with the prime-dilated short
reference gamma_pd(S) = min((1+S)/2, 3/4 - S, (6+S)/11) (Walls.lean form: (3/4 + g/2 - B) + (L-2)S - 9/2 a S > 0 at S = cap).
Then theta* at the end face with worth.theta_star (h = 0.8097)."""
import sys, os, io, contextlib
sys.path.insert(0, '/home/user/QuasiRiemannTracker/research/fresh-look/second/base_models')
sys.dont_write_bytecode = True

def run(K, c6, B=0.99999, L0=3.72, c0=0.06, h=1e-4, ref='pd'):
    L, c = L0, c0
    while True:
        Ln = L - h
        den = L * (1 + K) - c6 * K * B
        if den <= 0:
            return L, c, 'overshoot'
        a = K * h / den * (1 + 1e-9)
        if a > (Ln - 1) / (c6 - 2):
            return L, c, 'selected branch'
        cn = c / (1 - a + c6 * a * c) * (1 - 1e-12)
        S = cn
        g = min((1 + S) / 2, 3 / 4 - S, (6 + S) / 11) if ref == 'pd' else 0.5
        ok = {'principal': (3 / 4 + g / 2 - B) + (Ln - 2) * S - 4.5 * a * S > 0,
              'diagonal': Ln - 1 - 4 * a > 0, 'secondRef': 1.5 * Ln - 2.5 - 4.5 * a > 0,
              'refPos': 1 / 6 - (1 + 1.5 * a) * cn > 0, 'H': 1 - c6 * a * cn > 0, 'cap_lt': c < 1 / 6}
        bad = [k for k, v in ok.items() if not v]
        if bad:
            return L, c, ','.join(bad)
        L, c = Ln, cn

with contextlib.redirect_stdout(io.StringIO()):
    import worth
bar = 0.8733819666133 - 5e-5
for c6 in (6.0, 5.95, 5.9, 5.85, 5.8, 5.7, 5.5):
    for ref in ('half', 'pd'):
        L, cap, why = run(0.500001, c6, ref=ref)
        t = worth.theta_star(5/6, L=L, B=0.99999, h=0.8097)[0]
        print('c=%.2f ref=%-4s: line ends at L=%.4f (%s), cap %.4f; theta* %.8f (vs bar %+.2e)' % (c6, ref, L, why, cap, t, t - bar), flush=True)
