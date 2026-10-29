"""Assemble /home/user/QuasiRiemannTracker/research/newpowers/TA_ceiling.md from results/*.json and logs/*.log (numbers are read, not typed)."""
import glob, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
OUT = os.path.join(os.path.dirname(HERE), 'TA_ceiling.md')
BAR = 0.8739058
REC = 0.8739558
R = os.path.join(HERE, 'results')
L = os.path.join(HERE, 'logs')


def jl(name):
    fn = os.path.join(R, name)
    return json.load(open(fn)) if os.path.exists(fn) else None


def disc(g, f, b, d, K=8):
    return jl('e2_g%g_f%.2f_b%d_d%.3f_dL0.005_q%s.json' % (g, f, b, d, '' if K == 8 else '_K%d' % K))


def ode(g, f, b, d):
    return jl('e2_ode2_g%g_f%.2f_b%d_d%.3f.json' % (g, f, b, d))


def gap(r):
    return 1e6 * (r['theta'] - BAR)


def th(r):
    return '%.9f' % r['theta']


def cg(r):
    return '-' if r is None else '%.7f (%+.1f)' % (r['theta'], gap(r))


def readlog(name):
    fn = os.path.join(L, name)
    return open(fn).read() if os.path.exists(fn) else ''


def table(getter, gain, floors, sets=None):
    sets = sets or [('base (native 3/4, 0.999)', 0, 0.999), ('+ bootstrap', 1, 0.999), ('+ 0.999 -> 1', 0, 1.0), ('all-on', 1, 1.0)]
    out = ['| setting | ' + ' | '.join('floor %.2f' % f for f in floors) + ' |', '|---|' + '---|' * len(floors)]
    for nm, b, d in sets:
        out.append('| %s | %s |' % (nm, ' | '.join(cg(getter(gain, f, b, d)) for f in floors)))
    return '\n'.join(out)


def lev(f, which='g1', b=1, d=1.0):
    return jl('lev2_g1_f%.2f_b%d_d%.3f.json' % (f, b, d))


if __name__ == '__main__':
    print(table(disc, 1.0, (0.60, 0.55, 0.50)))
    print(lev(0.60))
