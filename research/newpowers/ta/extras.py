"""Extra scenarios (run after the main batches):  python3 extras.py {fine|decomp|sigma|hypo|sens} [nproc]"""
import sys, os, time, json
from multiprocessing import Pool
import run_ode, run_scenario, sens

FLOORS = (0.60, 0.55, 0.50)


def t_fine(a):
    var, floor, dL = a
    t0 = time.time()
    r = run_scenario.run_discrete(var, floor, True, 1.0, dL)
    print('%-34s theta=%.9f gap=%+.2e C(L=%.4f,s0=%.4f,idx %d/%d) P(L=%.3f) [%.0fs]' % (
        r['name'], r['theta'], r['theta'] - 0.8739058, r['C']['L'], r['C']['s0'], r['C']['idx'], r['nsteps'], r['P']['L'], time.time() - t0), flush=True)


def t_decomp(a):
    var, boot, dfac, floor = a
    run_ode.run_ode(var, bool(boot), dfac, floors=(floor,))


def t_sigma(a):
    var, sigma, floor = a
    run_ode.run_ode(var, False, 0.999, floors=(floor,), sigma=sigma, tag='_sig%g' % sigma)


def t_floorscan(a):
    var, = a
    fl = (0.59, 0.58, 0.57, 0.56, 0.54, 0.53, 0.52, 0.51)
    run_ode.run_ode(var, True, 1.0, floors=fl, tag='_scan')


def t_hypo(a):
    var, floor = a
    run_ode.run_ode(var, True, 1.0, floors=(floor,), tag='_hypo')


def t_sens(a):
    kind, var, floor = a
    if kind == 'whole':
        r = sens.sens(var, floor)
        print('%-4s floor %.2f all-on: theta0=%.9f theta(R-2e-3)=%.9f dtheta/dR=%.4e C L %.3f->%.3f' % (
            var, floor, r[0], r[1], r[2], r[3]['C']['L'], r[4]['C']['L']), flush=True)
    else:
        wins = [(2.58, 2.45), (2.45, 2.30), (2.30, 2.15), (2.15, 1.80)]
        a0, out = sens.window_sens(var, floor, wins)
        for (w, t, s) in out:
            print('%-4s floor %.2f window L in [%.2f,%.2f]: theta0=%.9f theta=%.9f dtheta/dR=%.4e' % (var, floor, w[1], w[0], a0, t, s), flush=True)


if __name__ == '__main__':
    mode = sys.argv[1]
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    if mode == 'fine':
        tasks = [(v, f, 0.0025) for v in ('d2', 'b1', 'a', 'd1') for f in FLOORS]
        fn = t_fine
    elif mode == 'decomp':
        tasks = [(v, b, d, f) for v in ('a', 'd2') for f in (0.60, 0.50) for (b, d) in ((1, 0.999), (0, 1.0))]
        fn = t_decomp
    elif mode == 'sigma':
        tasks = [('a', 0.12, f) for f in (0.60, 0.55)] + [('a', 0.09, 0.60)]
        fn = t_sigma
    elif mode == 'floorscan':
        tasks = [(v,) for v in ('b1', 'd1', 'd2', 'a')]
        fn = t_floorscan
    elif mode == 'hypo':
        tasks = [(v, f) for v in ('d2', 'b1') for f in (0.45, 0.40)]
        fn = t_hypo
    elif mode == 'sens':
        tasks = [('whole', v, f) for v in ('a', 'b1', 'd2') for f in FLOORS] + [('win', v, 0.50) for v in ('d2', 'b1')]
        fn = t_sens
    with Pool(nproc) as p:
        p.map(fn, tasks, chunksize=1)
