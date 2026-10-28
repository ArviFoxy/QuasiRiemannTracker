"""Print every table of the report (markdown) from results/*.json and logs/*.log."""
import glob, json, os, re, sys
HERE = os.path.dirname(os.path.abspath(__file__))
BAR = 0.8739058
R = os.path.join(HERE, 'results')


def jl(name):
    fn = os.path.join(R, name)
    return json.load(open(fn)) if os.path.exists(fn) else None


def disc(g, f, b, d, K=8):
    return jl('e2_g%g_f%.2f_b%d_d%.3f_dL0.005_q%s.json' % (g, f, b, d, '' if K == 8 else '_K%d' % K))


def ode(g, f, b, d):
    return jl('e2_ode2_g%g_f%.2f_b%d_d%.3f.json' % (g, f, b, d))


def c(r):
    return '-' if r is None else '%.7f (%+.1f)' % (r['theta'], 1e6 * (r['theta'] - BAR))


def faces(r):
    return '-' if r is None else '%.4f / %.3f' % (r['C']['L'], r['P']['L'])


def main_table(getter, gain, floors=(0.60, 0.55, 0.50)):
    sets = [('base: no bootstrap, 0.999', 0, 0.999), ('+ bootstrap', 1, 0.999), ('+ 0.999 -> 1', 0, 1.0), ('all-on', 1, 1.0)]
    out = ['| setting | ' + ' | '.join('floor %.2f' % f for f in floors) + ' |', '|---|' + '---|' * len(floors)]
    for nm, b, d in sets:
        out.append('| %s | %s |' % (nm, ' \\| '.join('') if False else ' | '.join(c(getter(gain, f, b, d)) for f in floors)))
    return '\n'.join(out)


if __name__ == '__main__':
    print('### discrete, marked (K = 8)\n'); print(main_table(disc, 1.0)); print()
    print('### discrete, gain off\n'); print(main_table(disc, 0.0, (0.65, 0.60, 0.55, 0.50))); print()
    print('### ODE, marked\n'); print(main_table(ode, 1.0)); print()
    print('### ODE, gain off\n'); print(main_table(ode, 0.0, (0.65, 0.60, 0.55, 0.50))); print()
    print('### ODE floor scan (marked)\n')
    for f in (0.60, 0.59, 0.58, 0.57, 0.56, 0.55, 0.50):
        print('floor %.2f: base %s | all-on %s' % (f, c(ode(1.0, f, 0, 0.999)), c(ode(1.0, f, 1, 1.0))))
    print('\n### faces (disc marked)\n')
    for f in (0.60, 0.55, 0.50):
        for (b, d) in ((0, 0.999), (1, 1.0)):
            r = disc(1.0, f, b, d)
            if r:
                print('floor %.2f b%d d%.3f: C idx %d/%d L=%.4f B=%.6f s0=%.4f | P idx %d L=%.4f B=%.6f s0=%.4f | h=%.6f ell=%.6f' % (
                    f, b, d, r['C']['idx'], r['nsteps'], r['C']['L'], r['C']['B'], r['C']['s0'], r['P']['idx'], r['P']['L'], r['P']['B'], r['P']['s0'], r['h'], 11 / 3 - 4 * r['theta']))
    print('\n### K scan (all-on, disc)\n')
    for f in (0.60, 0.55, 0.50):
        print('floor %.2f: K=1 %s | K=2 %s | K=8 %s' % (f, c(disc(1.0, f, 1, 1.0, 1)), c(disc(1.0, f, 1, 1.0, 2)), c(disc(1.0, f, 1, 1.0, 8))))
