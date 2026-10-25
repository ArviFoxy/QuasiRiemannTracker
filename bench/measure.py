"""Measure the compile cost of each submission's proof.

A module's cost is the CPU time (user + system) of one clean `lean` run on it,
less the time Lean reports for importing its dependencies and starting up.
That fixed price is paid by every module, however small, so counting it would
make the cost a function of how a proof is split into files rather than of the
proof. A submission's cost is the sum over the modules of its import closure.
A module shared by several submissions (the OpenAI baseline, or code carried
over from a predecessor) is compiled and measured once: modules are content
addressed by their source and the keys of their dependencies, as in the
verifier's build cache.

Submitted Lean is untrusted code: every compile runs as an unprivileged user,
without network access and with a scrubbed environment.

  python3 bench/measure.py stats                  unique work across submissions
  python3 bench/measure.py run [--workers 3] [--fast] [ID...]
  python3 bench/measure.py status
  python3 bench/measure.py dump [ID...]           declaration graphs of built submissions

With --fast the modules are only built, not measured: no profiler, no kernel
type checking (the compiled files are the same), no repeats, one more worker. That is
enough for the alive code, which needs the compiled modules but not their cost.

Each finished submission also gets the declaration graph of its modules read from
the compiled files (bench/alive/Dump.lean), after which the compiled files that no
unfinished submission builds on are deleted, so that disk use follows the work in
progress rather than everything ever compiled.
"""
from concurrent.futures import ThreadPoolExecutor, wait, FIRST_COMPLETED
from pathlib import Path
import argparse, collections, datetime, gzip, hashlib, heapq, json, os, pwd, re, shutil, signal, subprocess, sys, threading, time

ROOT = Path(__file__).resolve().parents[1]
BENCH = Path(os.environ.get('QRH_BENCH_ROOT', ROOT/'.bench')).resolve()
PLANS, STORE, LIBS, SCRATCH = BENCH/'plans', BENCH/'store', BENCH/'libs', BENCH/'scratch'
MEASUREMENTS = BENCH/'measurements.jsonl'
DUMPS = BENCH/'dumps'
DUMPER = ROOT/'bench/alive/Dump.lean'
STOP = BENCH/'STOP'
MIN_FREE = 2.5 * 1024 ** 3  # bytes; below this no new compile starts
SIDE_CAP = int(1.5 * 1024 ** 2)  # KiB of anonymous memory beside a heavy module
# Bump when the compiler command line or the products that are kept change.
RECIPE = 'lean-j1-prof-o-v1'
# Lean's profiler reports the phases of a run. Importing the dependencies and
# starting up are the fixed price every module pays, and are not counted. Time
# the main thread spends blocked on tasks repeats work the profiler already
# attributes to the task, so the sum of the remaining phases leaves it out.
STARTUP = ('import', 'initialization')
BLOCKED = 'blocked (unaccounted)'
# Teardown and bookkeeping outside the profiler's phases: CPU time net of
# startup exceeds the sum of the other phases by about this much on an
# undisturbed run (median 0.13 s, solo or with three compiles at once).
SLACK = 0.13
PRODUCTS = ('', '.private', '.server')
BASELINE = 'openai-baseline'
USER = 'qrhbench'
GIB = 1024 ** 2  # in KiB
ATTEMPTS = 3
CANARIES = 5
CANARY_EVERY = 1800  # seconds


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(',', ':'))


def digest(value):
    return hashlib.sha256(canonical(value).encode()).hexdigest()


def now():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def environment():
    path = BENCH/'environment.json'
    if not path.exists():
        raise SystemExit(f'Run bench/setup.py first: {path} is missing')
    return json.loads(path.read_text())


def environment_key(env):
    return digest({'recipe': RECIPE, 'lean': env['lean_sha256'], 'packages': env['packages'],
                   'platform': 'linux-x86_64'})


def load_plans():
    if not any(PLANS.glob('*.json')):
        subprocess.run(['node', str(ROOT/'bench/plan.mjs'), '--out', str(PLANS)], check=True, cwd=ROOT)
    return {plan['id']: plan for plan in (json.loads(p.read_text()) for p in sorted(PLANS.glob('*.json')))}


def module_keys(plan, env_key):
    keys = {}
    for module in plan['modules']:  # dependency-first
        keys[module['name']] = digest({
            'environment': env_key, 'module': module['name'], 'source': module['sha256'],
            'dependencies': {dep: keys[dep] for dep in sorted(module['dependencies'])}})
    return keys


class Job:
    def __init__(self, key, module):
        self.key, self.module, self.submissions = key, module, []
        self.dependencies = set()

    @property
    def relative(self):
        return self.module['name'].replace('.', '/')


def build_graph(plans, env_key):
    """Unique compile jobs across submissions, and each submission's job keys."""
    # Small submissions first, so shared prefixes are compiled early and reused.
    order = sorted(plans, key=lambda i: (i != BASELINE, len(plans[i]['modules']), i))
    jobs, members = {}, {}
    for sid in order:
        keys = module_keys(plans[sid], env_key)
        members[sid] = [keys[m['name']] for m in plans[sid]['modules']]
        for m in plans[sid]['modules']:
            job = jobs.get(keys[m['name']])
            if job is None:
                job = jobs[keys[m['name']]] = Job(keys[m['name']], m)
                job.dependencies = {keys[d] for d in m['dependencies']}
            job.submissions.append(sid)
    return order, jobs, members


def read_measurements():
    records = []
    if MEASUREMENTS.exists():
        lines = MEASUREMENTS.read_text().splitlines()
        for number, line in enumerate(lines):
            try:
                records.append(json.loads(line))
            except json.JSONDecodeError:
                # A run in progress may be appending; only its last line can be partial.
                if number != len(lines) - 1:
                    raise
    return records


def tolerance(net):
    return max(0.25, 0.04 * net)


def consistent(record):
    """Does the profiler's account of the run match the process's CPU time?

    A run that was preempted or read cold files shows time in the profiler's
    phases that the process never spent on a CPU, or the reverse.
    """
    return 'net' in record and abs(record['net'] - record['work'] - SLACK) <= tolerance(record['net'])


def best_costs(records):
    """For each module key, the successful measurement that agrees best with its profile."""
    best = {}
    for r in records:
        if r['kind'] in ('cost', 'repeat') and r['status'] == 'ok' and 'net' in r:
            quality = abs(r['net'] - r['work'] - SLACK)
            if r['key'] not in best or quality < best[r['key']][0]:
                best[r['key']] = (quality, r)
    return {key: record for key, (_, record) in best.items()}


def stats(plans):
    order, jobs, members = build_graph(plans, 'stats')
    total = sum(len(m) for m in members.values())
    print(f'{len(order)} submissions, {total} module instances, {len(jobs)} unique compile jobs '
          f'({100*len(jobs)/total:.0f}% of instances)')
    seen, lines_done = set(), 0
    print(f"{'submission':44} {'modules':>7} {'new':>6} {'new lines':>10}")
    for sid in order:
        new = [k for k in members[sid] if k not in seen]
        seen.update(new)
        new_lines = sum(jobs[k].module['lines'] for k in new)
        lines_done += new_lines
        print(f'{sid:44} {len(members[sid]):7d} {len(new):6d} {new_lines:10d}')
    print(f'unique lines to compile: {lines_done}  (baseline alone: '
          f"{sum(m['lines'] for m in plans[BASELINE]['modules'])})")


def unprivileged():
    """The account compiles run as, created on first use."""
    try:
        return pwd.getpwnam(USER)
    except KeyError:
        subprocess.run(['useradd', '--system', '--no-create-home', '--shell', '/usr/sbin/nologin', USER], check=True)
        return pwd.getpwnam(USER)


def confined(command, env):
    """Run as an unprivileged user without network, in an otherwise empty environment."""
    assignments = [f'{k}={v}' for k, v in env.items()]
    prefix = []
    if os.getuid() == 0:
        user = unprivileged()
        prefix = ['/usr/bin/unshare', '--net', '/usr/bin/setpriv', f'--reuid={user.pw_uid}',
                  f'--regid={user.pw_gid}', '--clear-groups', '--no-new-privs']
    # Compiles are batch work; keep interactive tools responsive.
    return [*prefix, '/usr/bin/nice', '-n', '5', '/usr/bin/env', '-i', *assignments, *command]


def anonymous_kib(pid):
    try:
        for line in Path(f'/proc/{pid}/status').read_text().splitlines():
            if line.startswith('RssAnon:'):
                return int(line.split()[1])
    except (OSError, ValueError):
        pass
    return 0


PHASE = re.compile(r'^\s+(\S.*?) ([0-9.]+(?:e-?[0-9]+)?)(ns|us|µs|ms|s)$')
UNITS = {'ns': 1e-9, 'us': 1e-6, 'µs': 1e-6, 'ms': 1e-3, 's': 1.0}


def parse_profile(text):
    """Seconds spent in each phase, from the summary Lean prints under -Dprofiler=true."""
    marker = text.rfind('cumulative profiling times:')
    if marker < 0:
        return None
    phases = {}
    for line in text[marker:].splitlines()[1:]:
        match = PHASE.match(line)
        if match:
            phases[match.group(1)] = float(match.group(2)) * UNITS[match.group(3)]
    return phases or None


class Guard(threading.Thread):
    """Stops a compile that outgrows its memory or time budget."""

    def __init__(self, proc, anon_cap_kib, timeout):
        super().__init__(daemon=True)
        self.proc, self.cap, self.timeout = proc, anon_cap_kib, timeout
        self.finished, self.reason, self.peak_anon_kib = threading.Event(), None, 0

    def run(self):
        started = time.monotonic()
        while not self.finished.wait(0.5):
            self.peak_anon_kib = max(self.peak_anon_kib, anonymous_kib(self.proc.pid))
            if self.peak_anon_kib > self.cap:
                self.reason = 'memory'
            elif time.monotonic() - started > self.timeout:
                self.reason = 'timeout'
            if self.reason:
                try:
                    os.killpg(self.proc.pid, signal.SIGKILL)
                except ProcessLookupError:
                    pass
                return


def compile_module(job, view, env, *, anon_cap_kib, timeout, attempt=1, keep=True, fast=False):
    """Compile one module once and measure the whole process. Returns a record."""
    user = unprivileged() if os.getuid() == 0 else None
    scratch = SCRATCH/f'{job.key[:16]}-{attempt}-{os.getpid()}-{threading.get_ident()}'
    if scratch.exists():
        shutil.rmtree(scratch)
    for part in ['out', 'home', 'tmp']:
        (scratch/part).mkdir(parents=True)
    if user:
        for path in [scratch, *scratch.iterdir()]:
            os.chown(path, user.pw_uid, user.pw_gid)
    lean = Path(env['lean'])/'bin/lean'
    libraries = ':'.join([str(view), *env['libraries']])
    # The kernel's check changes nothing in what is written, so a build can skip it.
    flags = ['-j1', '-Ddebug.skipKernelTC=true'] if fast else ['-j1', '-Dprofiler=true', '-Dprofiler.threshold=100000000']
    # The .ilean file says where every name in the source points, which is what the
    # alive code needs to know about what the text of a declaration mentions.
    command = [str(lean), *flags, '-o', str(scratch/'out/module.olean'), '-i', str(scratch/'out/module.ilean'),
               job.relative+'.lean']
    environment = {'PATH': f"{lean.parent}:/usr/bin:/bin", 'HOME': str(scratch/'home'), 'TMPDIR': str(scratch/'tmp'),
                   'LANG': 'C.UTF-8', 'LEAN_ABORT_ON_PANIC': '1', 'LEAN_PATH': libraries}
    record = {'key': job.key, 'module': job.module['name'], 'owner': job.module['owner'], 'attempt': attempt,
              'lines': job.module['lines'], 'started_at': now(), **({'mode': 'fast'} if fast else {})}
    log = (scratch/'log').open('wb')
    try:
        started = time.monotonic()
        proc = subprocess.Popen(confined(command, environment), cwd=ROOT/'submissions'/job.module['owner']/'src',
                                env={}, stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                                start_new_session=True)
        try:  # Let the kernel pick this process first if memory runs out.
            Path(f'/proc/{proc.pid}/oom_score_adj').write_text('1000')
        except OSError:
            pass
        guard = Guard(proc, anon_cap_kib, timeout)
        guard.start()
        _, status, usage = os.wait4(proc.pid, 0)
        wall = time.monotonic() - started
        guard.finished.set()
        proc.returncode = os.waitstatus_to_exitcode(status)
        record.update(wall=round(wall, 3), cpu_user=round(usage.ru_utime, 3), cpu_system=round(usage.ru_stime, 3),
                      maxrss_kib=usage.ru_maxrss, peak_anon_kib=guard.peak_anon_kib, exit=proc.returncode)
        output = scratch/'out/module.olean'
        text = (scratch/'log').read_bytes()[-16384:].decode('utf-8', 'replace')
        if guard.reason:
            record['status'] = 'memory' if guard.reason == 'memory' else 'timeout'
        elif proc.returncode == -signal.SIGKILL:
            # Nothing of ours stopped it, so the kernel ran out of memory.
            record['status'] = 'memory'
        elif proc.returncode or not output.is_file() or output.is_symlink():
            record['status'] = 'failed'
            record['log'] = text[-3000:]
        else:
            record['status'] = 'ok'
            profile = parse_profile(text)
            if profile and all(p in profile for p in ('import',)):
                total = record['cpu_user'] + record['cpu_system']
                record['profile'] = {k: round(v, 4) for k, v in sorted(profile.items())}
                record['net'] = round(total - sum(profile.get(p, 0.0) for p in STARTUP), 3)
                record['work'] = round(sum(v for k, v in profile.items() if k not in (*STARTUP, BLOCKED)), 3)
            if keep:
                entry = STORE/job.key
                if entry.exists():
                    shutil.rmtree(entry)
                entry.mkdir(parents=True)
                for suffix in PRODUCTS:
                    product = Path(str(output)+suffix)
                    if product.is_symlink():
                        raise RuntimeError('Symlink compiler output')
                    if product.exists():
                        os.rename(product, entry/('module.olean'+suffix))
                        record['store_bytes'] = record.get('store_bytes', 0) + (entry/('module.olean'+suffix)).stat().st_size
                references = scratch/'out/module.ilean'
                if references.is_symlink():
                    raise RuntimeError('Symlink compiler output')
                if references.exists():
                    os.rename(references, entry/'module.ilean')
        return record
    finally:
        log.close()
        shutil.rmtree(scratch, ignore_errors=True)


def measure_module(job, view, env, *, anon_cap_kib, timeout, canary=False, fast=False):
    """Compile a module, repeating a run whose CPU time and profile disagree."""
    records = []
    for attempt in range(1, ATTEMPTS+1):
        record = compile_module(job, view, env, anon_cap_kib=anon_cap_kib, timeout=timeout, attempt=attempt,
                                keep=not canary and attempt == 1, fast=fast)
        records.append(record)
        if fast or record['status'] != 'ok' or consistent(record):
            break
    return records


def link_views(job, skip=()):
    """Make a built module importable from every submission view that contains it."""
    entry = STORE/job.key
    for sid in job.submissions:
        if sid in skip:
            continue
        for suffix in PRODUCTS:
            source = entry/('module.olean'+suffix)
            if source.exists():
                target = LIBS/sid/(job.relative+'.olean'+suffix)
                target.parent.mkdir(parents=True, exist_ok=True)
                if target.exists():
                    if os.path.samefile(source, target):
                        continue
                    target.unlink()
                os.link(source, target)


def is_built(key):
    """A module is built when its compiled file and its name references are both kept."""
    return (STORE/key/'module.olean').exists() and (STORE/key/'module.ilean').exists()


def text_references(path, modules):
    """What the source of each declaration names, from the compiler's .ilean file.

    Returns pairs (declaration, constant) and the constants named outside any
    declaration (an `attribute [simp] foo`), for constants of the given modules.
    """
    data = json.loads(Path(path).read_text())
    pairs, context = set(), set()
    for reference, info in data.get('references', {}).items():
        named = json.loads(reference).get('c')
        if not named or named['m'] not in modules:
            continue
        for usage in info.get('usages', []):
            if len(usage) > 4:
                if usage[4] != named['n']:
                    pairs.add((usage[4], named['n']))
            else:
                context.add(named['n'])
    return sorted(pairs), sorted(context)


def is_complete(sid, keys, measured, costs=True):
    """Is the submission measured (unless only built), with the declaration graph of every module kept?"""
    return ((not costs or all(k in measured for k in keys)) and (DUMPS/'index'/f'{sid}.json').exists()
            and all((DUMPS/f'{k}.json.gz').exists() for k in keys))


def unneeded(order, members, finished, sid):
    """Compiled modules of a submission that no unfinished submission builds on."""
    needed = {k for t in order if t not in finished for k in members[t]}
    return [k for k in members[sid] if k not in needed]


def dump_submission(sid, plan, keys, env, *, anon_cap_kib=10*GIB, timeout=3600):
    """Keep the declaration graph of each module of a built submission that has none.

    The graphs are what the alive code is worked out from, offline, so the compiled
    files can go once they exist. Returns whether every module has one.
    """
    (DUMPS/'index').mkdir(parents=True, exist_ok=True)
    pending = {k for k in keys if not (DUMPS/f'{k}.json.gz').exists()}
    if pending:
        user = unprivileged() if os.getuid() == 0 else None
        scratch = SCRATCH/f'dump-{sid}-{os.getpid()}'
        shutil.rmtree(scratch, ignore_errors=True)
        for part in ['out', 'home', 'tmp']:
            (scratch/part).mkdir(parents=True)
        if user:
            for path in [scratch, *scratch.iterdir()]:
                os.chown(path, user.pw_uid, user.pw_gid)
        (scratch/'index.tsv').write_text(''.join(
            f"{m['name']}\t{STORE/k/'module.olean'}\t{k}\t{int(k in pending)}\n" for m, k in zip(plan['modules'], keys)))
        lean = Path(env['lean'])/'bin/lean'
        environment = {'PATH': f"{lean.parent}:/usr/bin:/bin", 'HOME': str(scratch/'home'), 'TMPDIR': str(scratch/'tmp'),
                       'LANG': 'C.UTF-8'}
        log = (scratch/'log').open('wb')
        try:
            proc = subprocess.Popen(confined([str(lean), '--run', str(DUMPER), str(scratch/'index.tsv'), str(scratch/'out')], environment),
                                    cwd=ROOT, env={}, stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                                    start_new_session=True)
            guard = Guard(proc, anon_cap_kib, timeout)
            guard.start()
            code = proc.wait()
            guard.finished.set()
            if code or guard.reason:
                print(f"declaration graph of {sid} failed ({guard.reason or code}): "
                      f"{(scratch/'log').read_text(errors='replace')[-600:]}", flush=True)
                return False
            names = {m['name'] for m in plan['modules']}
            for key in pending:
                source = scratch/'out'/f'{key}.json'
                if not source.is_file() or source.is_symlink():
                    print(f'declaration graph of {sid}: no output for {key}', flush=True)
                    return False
                graph = json.loads(source.read_bytes())
                graph['references'], graph['context'] = text_references(STORE/key/'module.ilean', names)
                temporary = DUMPS/f'{key}.json.gz.tmp'
                with gzip.open(temporary, 'wt', compresslevel=6) as write:
                    json.dump(graph, write, separators=(',', ':'))
                os.replace(temporary, DUMPS/f'{key}.json.gz')
        finally:
            log.close()
            shutil.rmtree(scratch, ignore_errors=True)
    # The submission's keys in module order, for reading its graphs back.
    index = DUMPS/'index'/f'{sid}.json'
    index.write_text(json.dumps(keys)+'\n')
    return True


def collect_garbage(sid, jobs, order, members, finished):
    """Delete the compiled modules of a finished submission that nobody builds on."""
    freed = 0
    for key in unneeded(order, members, finished, sid):
        job = jobs[key]
        for name in job.submissions:
            for suffix in PRODUCTS:
                (LIBS/name/(job.relative+'.olean'+suffix)).unlink(missing_ok=True)
        entry = STORE/key
        freed += sum(f.stat().st_size for f in entry.glob('*') if f.is_file())
        shutil.rmtree(entry, ignore_errors=True)
    shutil.rmtree(LIBS/sid, ignore_errors=True)
    return freed


class Runner:
    def __init__(self, env, order, jobs, members, targets, *, workers, anon_cap_kib, heavy_cap_kib, timeout,
                 plans=None, dump=False, collect=False, side_cap_kib=None, fast=False):
        self.env, self.order, self.jobs, self.members = env, order, jobs, members
        self.targets, self.workers = targets, workers
        self.anon_cap_kib, self.heavy_cap_kib, self.timeout = anon_cap_kib, heavy_cap_kib, timeout
        # Beside a module that needs most of the memory, others get only what almost
        # every module needs, so nothing is squeezed out of the page cache.
        self.side_cap_kib = side_cap_kib or min(anon_cap_kib, SIDE_CAP)
        self.plans, self.dump, self.collect, self.fast = plans, dump, collect, fast
        self.finished = set()
        self.lock = threading.Lock()
        self.last_warning = 0.0

    def finish(self, sid):
        """A submission is built: keep its declaration graphs, then release what nobody needs."""
        try:
            if not dump_submission(sid, self.plans[sid], self.members[sid], self.env):
                print(f'{sid}: compiled modules kept; run `measure.py dump {sid}` after fixing the dumper', flush=True)
                return
            self.finished.add(sid)
            if self.collect:
                freed = collect_garbage(sid, self.jobs, self.order, self.members, self.finished)
                print(f'{sid}: declaration graphs kept, {freed/2**30:.1f} GiB of compiled modules released', flush=True)
            else:
                print(f'{sid}: declaration graphs kept', flush=True)
        except Exception as error:  # Compiling must go on.
            print(f'{sid}: finishing failed: {error!r}', flush=True)

    def low_disk(self):
        free = shutil.disk_usage(BENCH).free
        if free >= MIN_FREE:
            return False
        if time.monotonic() - self.last_warning > 300:
            self.last_warning = time.monotonic()
            print(f'Only {free/2**30:.1f} GiB free: no new compiles until there is room', flush=True)
        return True

    def append(self, record):
        with self.lock, MEASUREMENTS.open('a') as stream:
            stream.write(json.dumps(record, sort_keys=True)+'\n')

    def choose_canaries(self, measured):
        """Mid-cost baseline modules, remeasured through the run to expose drift."""
        path = BENCH/'canaries.json'
        if path.exists():
            return json.loads(path.read_text())
        candidates = sorted((r['net'], k) for k, r in measured.items()
                            if self.jobs[k].module['owner'] == BASELINE and 3 <= r['net'] <= 15)
        if len(candidates) < 40:
            return []
        keys = [candidates[int(len(candidates)*q)][1] for q in (0.15, 0.35, 0.5, 0.7, 0.9)][:CANARIES]
        path.write_text(json.dumps(keys))
        return keys

    def run(self):
        for path in (SCRATCH, LIBS, STORE):
            path.mkdir(parents=True, exist_ok=True)
        measured = best_costs(read_measurements())
        # What is measured and has its declaration graphs needs nothing more, and its
        # compiled modules may be gone.
        self.finished = {sid for sid in self.targets
                         if self.dump and is_complete(sid, self.members[sid], measured, costs=not self.fast)}
        targets = [sid for sid in self.targets if sid not in self.finished]
        built = {k for k in self.jobs if is_built(k)}
        wanted = {k for sid in targets for k in self.members[sid]}
        for key in built & wanted:
            link_views(self.jobs[key], self.finished)
        todo = wanted - built
        remaining = {sid: len(set(self.members[sid]) - built) for sid in targets}
        rank = {sid: i for i, sid in enumerate(self.order)}
        priority = {}
        for sid in sorted(targets, key=rank.get, reverse=True):
            for index, key in enumerate(self.members[sid]):
                priority[key] = (rank[sid], index)
        waiting = {k: {d for d in self.jobs[k].dependencies if d in todo} for k in todo}
        dependents = collections.defaultdict(list)
        for key, deps in waiting.items():
            for dep in deps:
                dependents[dep].append(key)
        ready = [(priority[k], k) for k in todo if not waiting[k]]
        heapq.heapify(ready)
        heavy, deferred, running, failed, canaries = [], [], {}, set(), []
        total, finished, started = len(todo), 0, time.monotonic()
        spent = 0.0
        print(f'{len(wanted)} modules wanted, {len(built & wanted)} already built, {total} to compile', flush=True)
        last_report = last_canary = started
        canary_round = 0

        def start(pool, key, cap, canary=False):
            job = self.jobs[key]
            # Any view that holds the module's dependencies will do, and the views of
            # finished submissions are gone.
            view = LIBS/next((s for s in job.submissions if s not in self.finished), job.submissions[0])
            kind = 'canary' if canary else ('build' if self.fast else ('cost' if key not in measured else 'rebuild'))
            future = pool.submit(measure_module, job, view, self.env, anon_cap_kib=cap, timeout=self.timeout,
                                 canary=canary, fast=self.fast)
            # 1: an ordinary module, 2: one that needs the memory to itself, 3: beside such a module.
            level = 3 if cap == self.side_cap_kib and cap < self.anon_cap_kib else (2 if cap == self.heavy_cap_kib and not canary else 1)
            running[future] = (key, kind, level)

        with ThreadPoolExecutor(max_workers=self.workers) as pool, ThreadPoolExecutor(max_workers=1) as after:
            if self.dump:
                for sid in targets:
                    if not remaining[sid]:
                        after.submit(self.finish, sid)
            while ready or running or heavy or deferred:
                stopping = STOP.exists() or self.low_disk()
                solo = any(level == 2 for _, _, level in running.values())
                if not solo and deferred:
                    for key in deferred:
                        heapq.heappush(ready, (priority[key], key))
                    deferred.clear()
                if heavy and not running and not stopping:
                    start(pool, heavy.pop(0), self.heavy_cap_kib)
                elif not stopping and (solo or not heavy):
                    cap = self.side_cap_kib if solo else self.anon_cap_kib
                    if not solo and not self.fast:
                        if not canaries and measured:
                            canaries = self.choose_canaries(measured)
                        if canaries and len(running) < self.workers and time.monotonic() - last_canary > CANARY_EVERY:
                            last_canary = time.monotonic()
                            start(pool, canaries[canary_round % len(canaries)], cap, canary=True)
                            canary_round += 1
                    # Beside a heavy module one other compile runs, so the heavy one keeps the memory.
                    while ready and len(running) < (2 if solo else self.workers):
                        _, key = heapq.heappop(ready)
                        start(pool, key, cap)
                if not running:
                    break
                done, _ = wait(running, timeout=20, return_when=FIRST_COMPLETED)
                for future in done:
                    key, kind, level = running.pop(future)
                    records = future.result()
                    for number, record in enumerate(records):
                        record['kind'] = kind if number == 0 else ('canary' if kind == 'canary' else 'repeat')
                        record['workers'] = self.workers
                        self.append(record)
                    record = records[-1]
                    if kind == 'canary':
                        continue
                    if record['status'] == 'ok':
                        link_views(self.jobs[key], self.finished)
                        measured = best_costs(read_measurements()) if len(records) > 1 else measured
                        if 'net' in records[0]:
                            measured.setdefault(key, records[0])
                        finished += 1
                        spent += records[0].get('net', 0.0)
                        for sid in self.jobs[key].submissions:
                            if sid in remaining:
                                remaining[sid] -= 1
                                if not remaining[sid] and self.dump:
                                    after.submit(self.finish, sid)
                        for dependent in dependents[key]:
                            waiting[dependent].discard(key)
                            if not waiting[dependent] and dependent not in failed:
                                heapq.heappush(ready, (priority[dependent], dependent))
                    elif record['status'] == 'memory' and level == 3:
                        # Beside a heavy module it had less room; try again once that one is done.
                        deferred.append(key)
                    elif record['status'] == 'memory' and level == 1:
                        print(f"memory cap hit by {record['module']} ({record['peak_anon_kib']//1024} MiB); retrying alone", flush=True)
                        heavy.append(key)
                    else:
                        failed.add(key)
                        print(f"FAILED {record['module']} ({record['status']}): {record.get('log', '')[-400:]}", flush=True)
                if time.monotonic() - last_report > 60:
                    last_report = time.monotonic()
                    print(f'[{(last_report-started)/60:7.1f} min] {finished}/{total} compiled, {len(running)} running, '
                          f'{spent/3600:.2f} net CPU-hours so far', flush=True)
        print(f'finished: {finished}/{total} compiled, {len(failed)} failed', flush=True)
        return not failed and finished == total


def status(env, plans):
    order, jobs, members = build_graph(plans, environment_key(env))
    costs = best_costs(read_measurements())
    print(f"{'submission':44} {'modules':>7} {'measured':>8} {'net cpu-hours':>14}")
    for sid in order:
        have = [k for k in members[sid] if k in costs]
        print(f"{sid:44} {len(members[sid]):7d} {len(have):8d} {sum(costs[k]['net'] for k in have)/3600:14.2f}")


def main():
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest='command', required=True)
    sub.add_parser('stats')
    sub.add_parser('status')
    dump = sub.add_parser('dump')
    dump.add_argument('ids', nargs='*')
    run = sub.add_parser('run')
    run.add_argument('ids', nargs='*')
    run.add_argument('--keep', action='store_true', help='keep the compiled modules of finished submissions')
    run.add_argument('--no-dump', action='store_true', help='skip the declaration graphs (and so the clean-up)')
    run.add_argument('--fast', action='store_true', help='only build: no profile, no kernel check, no repeats')
    run.add_argument('--workers', type=int, default=3)
    run.add_argument('--anon-cap-gib', type=float, default=4.5)
    run.add_argument('--heavy-cap-gib', type=float, default=11)
    run.add_argument('--timeout', type=int, default=7200)
    args = parser.parse_args()
    plans = load_plans()
    if args.command == 'stats':
        stats(plans)
        return
    env = environment()
    if args.command == 'status':
        status(env, plans)
    elif args.command == 'dump':
        order, jobs, members = build_graph(plans, environment_key(env))
        for sid in args.ids or order:
            if sid not in plans:
                raise SystemExit(f'Unknown submission: {sid}')
            missing = [k for k in members[sid] if not is_built(k)]
            if missing:
                print(f'{sid}: {len(missing)} of {len(members[sid])} modules are not compiled here', flush=True)
            elif dump_submission(sid, plans[sid], members[sid], env):
                print(f'{sid}: declaration graphs kept', flush=True)
    elif args.command == 'run':
        unknown = set(args.ids) - set(plans)
        if unknown:
            raise SystemExit(f'Unknown submissions: {sorted(unknown)}')
        order, jobs, members = build_graph(plans, environment_key(env))
        targets = args.ids or order
        STOP.unlink(missing_ok=True)
        runner = Runner(env, order, jobs, members, targets, workers=args.workers,
                        anon_cap_kib=int(args.anon_cap_gib*GIB), heavy_cap_kib=int(args.heavy_cap_gib*GIB),
                        timeout=args.timeout, plans=plans, dump=not args.no_dump,
                        collect=not (args.keep or args.no_dump), fast=args.fast)
        sys.exit(0 if runner.run() else 1)


if __name__ == '__main__':
    main()
