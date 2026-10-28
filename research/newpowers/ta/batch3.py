"""Main grid, second generation:  python3 batch3.py [nproc]
12 discrete scenarios: floors {0.60, 0.55, 0.50} x {base, boot only, 0.999->1 only, all-on}, gain = 1 (K = 8 Lean gain)
plus gain-off references at the same settings (PR 83/86 gate) for floors 0.65 / 0.60."""
import sys, time
from multiprocessing import Pool
import run2

TASKS = []
for f in (0.50, 0.55, 0.60):                       # longest chains first
    for (b, d) in ((0, 0.999), (1, 1.0), (1, 0.999), (0, 1.0)):
        TASKS.append((1.0, f, b, d))
for f in (0.60,):
    for (b, d) in ((0, 0.999), (1, 1.0)):
        TASKS.append((0.0, f, b, d))


def job(a):
    gain, floor, boot, dfac = a
    t0 = time.time()
    r = run2.run_scenario(gain, floor, boot, dfac, 0.005)
    print('%-44s theta=%.9f gap=%+.2e  C(L=%.4f,s0=%.4f,%d/%d) P(L=%.3f) [chain %.0fs, return %.0fs]' % (
        r['name'], r['theta'], r['theta'] - run2.BAR, r['C']['L'], r['C']['s0'], r['C']['idx'], r['nsteps'], r['P']['L'],
        r['t_chain'], r['t_ret']), flush=True)
    return r['name']


if __name__ == '__main__':
    nproc = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    with Pool(nproc) as p:
        for _ in p.imap_unordered(job, TASKS, chunksize=1):
            pass
