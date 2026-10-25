"""Prepare the Lean environment used to measure compile cost.

Mirrors verifier/actions/setup.py (same pins, same package patches) without the
sandbox, the judge toolchain or the kernels: the benchmark only compiles.
"""
from pathlib import Path
import hashlib, json, os, re, shlex, subprocess, sys, time

ROOT = Path(__file__).resolve().parents[1]
BENCH = Path(os.environ.get('QRH_BENCH_ROOT', ROOT/'.bench')).resolve()
PINS = json.loads((ROOT/'verifier/pins.json').read_text())
sha = lambda p: hashlib.file_digest(open(p, 'rb'), 'sha256').hexdigest()

# The verifier owns the source toolchain pin; read it instead of repeating it.
VERSION, DIGEST = re.search(r"source = toolchain\('([^']+)','([0-9a-f]{64})'\)",
                            (ROOT/'verifier/actions/setup.py').read_text()).groups()
assert PINS['lean'] == 'leanprover/lean4:v'+VERSION


def run(*args, cwd=None, env=None):
    command = list(map(str, args))
    print('bench setup: '+shlex.join(command[:8])+(f' ... ({len(command)-8} more)' if len(command) > 8 else ''), flush=True)
    started = time.monotonic()
    subprocess.run(command, cwd=cwd, env=env, check=True)
    print(f'bench setup: done in {time.monotonic()-started:.1f}s', flush=True)


def clone(url, rev, dest):
    if not dest.exists():
        run('git', 'init', '-q', dest)
        run('git', '-C', dest, 'fetch', '-q', '--depth=1', url, rev)
        run('git', '-C', dest, 'checkout', '-q', '--detach', 'FETCH_HEAD')
    if subprocess.check_output(['git', '-C', str(dest), 'rev-parse', 'HEAD'], text=True).strip() != rev:
        raise RuntimeError('Dependency revision differs: '+str(dest))


def toolchain():
    dest = BENCH/f'lean-{VERSION}-linux'
    if not dest.exists():
        archive = BENCH/(VERSION+'.tar.zst')
        run('curl', '--fail', '--location', '--retry', '3', '--proto', '=https', '--tlsv1.2', '-sS',
            f'https://github.com/leanprover/lean4/releases/download/v{VERSION}/lean-{VERSION}-linux.tar.zst', '-o', archive)
        if sha(archive) != DIGEST:
            raise RuntimeError('Toolchain archive checksum mismatch')
        run('tar', '--zstd', '-xf', archive, '-C', BENCH)
        archive.unlink()
    return dest


def package_modules():
    """Pinned-package modules imported anywhere in the repository's submissions."""
    plan = subprocess.run(['node', str(ROOT/'bench/plan.mjs'), '--package-imports'], cwd=ROOT,
                          check=True, capture_output=True, text=True)
    return json.loads(plan.stdout)


def main():
    BENCH.mkdir(parents=True, exist_ok=True)
    lean = toolchain()
    env = {**os.environ, 'PATH': str(lean/'bin')+':'+os.environ['PATH']}
    project = BENCH/'project'
    project.mkdir(exist_ok=True)
    manifest = (ROOT/'verifier/standard/lake-manifest.json').read_text()
    (project/'lake-manifest.json').write_text(manifest)
    (project/'lakefile.lean').write_text((ROOT/'verifier/standard/lakefile.lean').read_text())
    (project/'lean-toolchain').write_text(PINS['lean']+'\n')
    packages = project/'.lake/packages'
    packages.mkdir(parents=True, exist_ok=True)
    for p in json.loads(manifest)['packages']:
        name = p['name'].strip('«»')
        dest = packages/name
        clone(p['url'], p['rev'], dest)
        if name in ['rellich-kondrachov', 'PrimeNumberTheoremAnd']:
            patch = ROOT/'verifier/actions/patches'/(name+'-lean4341.patch')
            if subprocess.run(['git', '-C', str(dest), 'apply', '--reverse', '--check', str(patch)], capture_output=True).returncode:
                run('git', '-C', dest, 'apply', patch)
    # The official Mathlib cache supplies Mathlib and its dependencies.
    run(lean/'bin/lake', 'exe', 'cache', 'get', cwd=project, env=env)
    package_roots = {'PrimeNumberTheoremAnd', 'RellichKondrachov'}
    modules = package_modules()
    for module in modules:
        parts = module.split('.')
        if parts[0] not in package_roots or any(not part.isascii() or not part.isidentifier() for part in parts):
            raise RuntimeError('Invalid pinned package import')
    if modules:
        run(lean/'bin/lake', 'build', *sorted(set(modules)), cwd=project, env=env)
    # Import Mathlib exactly as the canonical challenge does.
    (project/'Challenge.lean').write_text('import Mathlib\n')
    run(lean/'bin/lake', 'build', 'Challenge', cwd=project, env=env)
    (project/'Challenge.lean').unlink()
    for p in (project/'.lake/build').rglob('Challenge.*'):
        p.unlink()
    libraries = sorted(p.resolve() for p in packages.glob('*/.lake/build/lib/lean') if p.is_dir())
    # Compiles run as an unprivileged user; the extracted cache is owner-only.
    run('chmod', '-R', 'a+rX', *libraries)
    (BENCH/'environment.json').write_text(json.dumps({
        'lean': str(lean), 'lean_version': VERSION, 'lean_sha256': sha(lean/'bin/lean'),
        'libraries': list(map(str, libraries)),
        'packages': {p['name'].strip('«»'): p['rev'] for p in json.loads(manifest)['packages']},
    }, indent=2)+'\n')
    print('Benchmark environment ready', flush=True)


if __name__ == '__main__':
    main()
