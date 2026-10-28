"""Run the scenario grid in parallel (multiprocessing).  usage: python3 batch.py {ode|disc|extra} [nproc]"""
import sys, os, json, time
from multiprocessing import Pool
import run_ode, run_scenario

VARS = ['pr83', 'a', 'b0', 'b1', 'c', 'cu', 'u', 'd1', 'd2', 'd3', 'd4']
FLOORS = (0.60, 0.55, 0.50)
SETS = [(0, 0.999), (1, 1.0)]


def task_ode(a):
    var, boot, dfac = a
    return run_ode.run_ode(var, bool(boot), dfac, FLOORS)


def task_disc(a):
    var, floor, boot, dfac, dL = a
    t0 = time.time()
    r = run_scenario.run_discrete(var, floor, bool(boot), dfac, dL)
    print('%-34s theta=%.9f gap=%+.2e  C(L=%.4f,s0=%.4f,idx %d/%d) P(L=%.3f) [%.0fs]' % (
        r['name'], r['theta'], r['theta'] - 0.8739058, r['C']['L'], r['C']['s0'], r['C']['idx'], r['nsteps'], r['P']['L'], time.time() - t0), flush=True)
    return r['name']


if __name__ == '__main__':
    mode = sys.argv[1]
    nproc = int(sys.argv[2]) if len(sys.argv) > 2 else 4
    if mode == 'ode':
        tasks = [(v, b, d) for v in VARS for (b, d) in SETS]
        with Pool(nproc) as p:
            p.map(task_ode, tasks, chunksize=1)
    elif mode == 'disc':
        dL = float(sys.argv[3]) if len(sys.argv) > 3 else 0.005
        tasks = [(v, f, b, d, dL) for v in VARS for f in FLOORS for (b, d) in SETS]
        with Pool(nproc) as p:
            p.map(task_disc, tasks, chunksize=1)
