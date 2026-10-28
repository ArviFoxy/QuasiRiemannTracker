"""Second wave: gain-off ladder at floors 0.55/0.50, K = 1 and 2 copies (all-on), ODE grid.   python3 batch4.py [nproc]"""
import sys, time
from multiprocessing import Pool
import run2, run_ode2

T = []
for (g, b, d, fl) in ((1.0, 0, 0.999, (0.60, 0.55, 0.50)), (1.0, 1, 1.0, (0.60, 0.55, 0.50)),
                      (1.0, 1, 0.999, (0.60, 0.55, 0.50)), (1.0, 0, 1.0, (0.60, 0.55, 0.50)),
                      (0.0, 0, 0.999, (0.65, 0.60, 0.55, 0.50)), (0.0, 1, 1.0, (0.65, 0.60, 0.55, 0.50))):
    T.append(('ode', g, fl, b, d, 8))
for (g, b, d) in ((1.0, 0, 0.999), (1.0, 1, 1.0)):
    T.append(('ode', g, (0.59, 0.58, 0.57, 0.56), b, d, 8))
for K in (1, 2):
    for f in (0.50, 0.55, 0.60):
        T.append(('disc', 1.0, f, 1, 1.0, K))


def job(a):
    kind = a[0]
    if kind == 'disc':
        _, gain, floor, boot, dfac, K = a
        r = run2.run_scenario(gain, floor, boot, dfac, 0.005, K=K)
        print('%-44s theta=%.9f gap=%+.2e  C(L=%.4f,s0=%.4f,%d/%d) P(L=%.3f) [chain %.0fs, return %.0fs]' % (
            r['name'], r['theta'], r['theta'] - run2.BAR, r['C']['L'], r['C']['s0'], r['C']['idx'], r['nsteps'], r['P']['L'],
            r['t_chain'], r['t_ret']), flush=True)
    else:
        _, gain, floors, boot, dfac, K = a
        run_ode2.run_ode(gain, bool(boot), dfac, floors=floors)
    return a


if __name__ == '__main__':
    nproc = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    with Pool(nproc) as p:
        for _ in p.imap_unordered(job, T, chunksize=1):
            pass
