"""ODE-limit grid:  python3 batch_ode2.py [nproc]   (marked gate, 4 settings x 3 floors; gain-off references)"""
import sys
from multiprocessing import Pool
import run_ode2

TASKS = [(1.0, 0, 0.999, (0.60, 0.55, 0.50)), (1.0, 1, 1.0, (0.60, 0.55, 0.50)),
         (1.0, 1, 0.999, (0.60, 0.55, 0.50)), (1.0, 0, 1.0, (0.60, 0.55, 0.50)),
         (0.0, 0, 0.999, (0.65, 0.60, 0.55, 0.50)), (0.0, 1, 1.0, (0.65, 0.60, 0.55, 0.50))]


def job(a):
    gain, boot, dfac, floors = a
    run_ode2.run_ode(gain, bool(boot), dfac, floors=floors)
    return a


if __name__ == '__main__':
    nproc = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    with Pool(nproc) as p:
        for _ in p.imap_unordered(job, TASKS, chunksize=1):
            pass
