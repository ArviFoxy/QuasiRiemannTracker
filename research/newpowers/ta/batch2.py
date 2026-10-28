"""Prioritised discrete scenarios (explicit order).  usage: python3 batch2.py [nproc] [dL]"""
import sys, time
from multiprocessing import Pool
import run_scenario
import batch

ORDER = []
def add(v, floors, sets=((0, 0.999), (1, 1.0))):
    for f in floors:
        for (b, d) in sets:
            ORDER.append((v, f, b, d))

add('d2', (0.60, 0.55, 0.50)); add('d1', (0.60, 0.55, 0.50)); add('b1', (0.60, 0.55, 0.50))
add('b0', (0.55,)); add('c', (0.60, 0.55)); add('u', (0.60, 0.55))
add('cu', (0.55,), sets=((1, 1.0),)); add('d3', (0.50,), sets=((1, 1.0),)); add('d4', (0.50,), sets=((1, 1.0),))

if __name__ == '__main__':
    nproc = int(sys.argv[1]) if len(sys.argv) > 1 else 4
    dL = float(sys.argv[2]) if len(sys.argv) > 2 else 0.005
    tasks = [(v, f, b, d, dL) for (v, f, b, d) in ORDER]
    with Pool(nproc) as p:
        for _ in p.imap_unordered(batch.task_disc, tasks, chunksize=1):
            pass
