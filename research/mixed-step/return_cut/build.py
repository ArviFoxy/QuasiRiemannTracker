"""Build every module of the package $QRH_PKG (return_cut.env) module by module, in dependency order.

Each module is compiled with `lake env lean -o <olean> -i <ilean> <file>` from the Lake project
(Lean 4.34.1 on PATH); oleans go to .lake/build/lib/lean/<package path>. Imports from outside the
package (Collet, baseline, PR 76's Graph.NaturalCap) must already be built. A module is rebuilt when
its olean is missing or older than its source or than a package dependency's olean. At most JOBS
Lean processes run at once (default 2); the dependents of a failed module are not started.
Per-module output goes to LOGDIR/<module>.log (default: return_cut/logs).

usage: (source return_cut.env) python3 build.py [JOBS [LOGDIR]]
"""
import os, subprocess, sys, time
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED

WS = '/home/user/lean-env/qrh'
PKG = os.environ['QRH_PKG']
ENV = dict(os.environ, PATH='/home/user/lean-env/lean-4.34.1-linux/bin:' + os.environ['PATH'])
HERE = os.path.dirname(os.path.abspath(__file__))
JOBS = int(sys.argv[1]) if len(sys.argv) > 1 else 2
LOGDIR = sys.argv[2] if len(sys.argv) > 2 else os.path.join(HERE, 'logs')


def src(m): return os.path.join(WS, m.replace('.', '/') + '.lean')
def olean(m): return os.path.join(WS, '.lake/build/lib/lean', m.replace('.', '/') + '.olean')


root = os.path.join(WS, PKG.replace('.', '/'))
mods = {}
for d, _, fs in os.walk(root):
    for f in fs:
        if f.endswith('.lean'):
            m = os.path.relpath(os.path.join(d, f), WS)[:-5].replace('/', '.')
            mods[m] = [l.split()[1] for l in open(src(m)) if l.startswith('import ') and l.split()[1].startswith(PKG + '.')]
missing = {d for ds in mods.values() for d in ds if d not in mods}
assert not missing, f'imports of missing package modules: {missing}'


def stale(m):
    o = olean(m)
    if not os.path.exists(o) or os.path.getmtime(src(m)) > os.path.getmtime(o):
        return True
    return any(os.path.getmtime(olean(d)) > os.path.getmtime(o) for d in mods[m])


def build(m):
    o = olean(m)[:-6]
    os.makedirs(os.path.dirname(o), exist_ok=True)
    t = time.time()
    r = subprocess.run(['lake', 'env', 'lean', '-o', o + '.olean', '-i', o + '.ilean', src(m)],
                       cwd=WS, env=ENV, capture_output=True, text=True)
    out = r.stdout + r.stderr
    open(os.path.join(LOGDIR, m + '.log'), 'w').write(out)
    return m, r.returncode, time.time() - t, out


os.makedirs(LOGDIR, exist_ok=True)
t0 = time.time()
done, rebuilt, fail, pending, running, cpu = set(), set(), [], set(mods), {}, 0.0
with ThreadPoolExecutor(max_workers=JOBS) as pool:
    while pending or running:
        for m in sorted(m for m in pending if set(mods[m]) <= done):
            if len(running) >= JOBS:
                break
            pending.remove(m)
            if not stale(m):
                done.add(m)
                continue
            running[pool.submit(build, m)] = m
        if not running:
            # up-to-date modules were only marked done: rescan unless nothing pending is ready
            if pending and not any(set(mods[m]) <= done for m in pending):
                print(f'blocked by failures: {len(pending)} modules')
                break
            continue
        fin, _ = wait(running, return_when=FIRST_COMPLETED)
        for f in fin:
            running.pop(f)
            m, rc, dt, out = f.result()
            cpu += dt
            if rc != 0:
                print(f'FAIL {m} ({dt:.0f}s)', flush=True)
                errs = [l for l in out.split('\n') if 'error' in l][:20]
                print('\n'.join(errs), flush=True)
                fail.append(m)
                pending = {p for p in pending if not any(d in fail for d in mods[p])}
            else:
                done.add(m)
                rebuilt.add(m)
                print(f'ok {m} ({dt:.0f}s)', flush=True)
wall = time.time() - t0
print(f'{len(rebuilt)} modules compiled, {len(done) - len(rebuilt)} up to date, wall {wall:.0f}s, '
      f'sum of module times {cpu:.0f}s')
print('ALL-OK' if not fail and len(done) == len(mods) else f'INCOMPLETE ({len(done)}/{len(mods)}, failed: {fail})')
