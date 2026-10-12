#!/usr/bin/env python3
"""Run a reviewed Lean proof in an offline Docker worker.

The operator supplies protected pins and paths. Canonical libraries and tool
trees are prepared and reviewed separately. Candidate files enter only after
the challenge has been exported and frozen. Each process receives an explicit
mount allowlist; the supervisor owns exports, logs and the final receipt.
"""
from pathlib import Path
import argparse
import datetime
import hashlib
import json
import os
import shutil
import subprocess
import sys

from sandbox import run, regular_inventory, require, real_path

HERE = Path(__file__).resolve().parent
AXIOMS = ['Classical.choice', 'Quot.sound', 'propext']
KERNELS = ['Lean default', 'nanoda', 'con-ron']


def sha(path):
    with Path(path).open('rb') as handle:
        return hashlib.file_digest(handle, 'sha256').hexdigest()


def write(path, value):
    Path(path).write_text(json.dumps(value, indent=2) + '\n')


def trusted_inventory(root):
    """Pin trusted tool trees, including their internal shared-library links."""
    root = real_path(root)
    result = {}
    for path in sorted(root.rglob('*')):
        name = path.relative_to(root).as_posix()
        if path.is_symlink():
            require(path.resolve().is_relative_to(root) and path.resolve().is_file(),
                    'Trusted link must resolve to a file inside its tool tree')
            result[name] = {'link': str(path.readlink())}
        elif path.is_file():
            result[name] = sha(path)
        else:
            require(path.is_dir(), 'Special trusted tool file')
    return result


def inventory(name, path):
    return (trusted_inventory if name.endswith('toolchain') else regular_inventory)(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--pins', type=Path, required=True)
    parser.add_argument('--profile', type=Path, required=True)
    parser.add_argument('--work', type=Path, required=True)
    args = parser.parse_args()
    pins = json.loads(args.pins.read_text())
    profile = json.loads(args.profile.read_text())
    work = args.work.absolute()
    work.mkdir()
    for name in ['logs', 'challenge-src', 'challenge-lib', 'candidate-src',
                 'candidate-lib', 'exports', 'config', 'scratch']:
        (work / name).mkdir()
    paths = {name: real_path(profile[name]) for name in
             ['source_toolchain', 'judge_toolchain', 'exporter', 'canonical_library',
              'candidate_dependencies', 'candidate_checkout', 'palomar', 'controls']}
    for name in ['source_toolchain', 'judge_toolchain', 'exporter', 'canonical_library',
                 'candidate_dependencies']:
        require(inventory(name, paths[name]) == pins['inventories'][name],
                f'{name} differs from reviewed inventory')
    require(sha(paths['palomar'] / 'scripts/verify_submission.py') ==
            'c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2',
            'Official Palomar controller differs')
    require(subprocess.check_output(['git', '-C', str(paths['candidate_checkout']),
                                    'rev-parse', 'HEAD'], text=True).strip() == pins['head_sha'],
            'Candidate checkout head differs')
    require(sha(HERE / pins['challenge_file']) == pins['challenge_sha256'],
            'Canonical challenge source differs')
    require(sha(paths['controls'] / 'control-results.json') == pins['controls_sha256'],
            'Checker controls differ')
    controls = json.loads((paths['controls'] / 'control-results.json').read_text())
    require(controls['status'] == 'PASS' and controls['image'] == pins['image'] and
            controls['sandbox_driver_sha256'] == sha(HERE / 'sandbox.py'),
            'Fresh controls for this sandbox and image required')
    sys.path.insert(0, str(paths['palomar']))
    from scripts.verify_submission import comparator_export_targets, primitive_targets
    config = {'challenge_module': 'Challenge', 'solution_module': 'Solution',
              'theorem_names': pins['targets'], 'definition_names': [],
              'permitted_axioms': AXIOMS,
              'external_kernels': {'nanoda': ['/judge/bin/nanoda_bin'],
                                   'con-ron': ['/judge/bin/con-ron', '--jobs=4']}}
    write(work / 'config/comparator.json', config)
    targets = comparator_export_targets(config, primitive_targets(paths['judge_toolchain']))
    environment = {'PATH': '/toolchain/bin:/usr/bin:/bin', 'HOME': '/tmp', 'TMPDIR': '/tmp',
                   'LANG': 'C.UTF-8', 'LEAN_NUM_THREADS': '1', 'LEAN_ABORT_ON_PANIC': '1'}
    phases = []

    def phase(name, command, readonly, writable=(), cwd='/tmp', env=None, timeout=1800,
              output=None, stream_limit=12*1024**2, check_output=True):
        result = run(image=pins['image'], command=command, readonly=readonly,
                     writable=writable, stdout=output or work/'logs'/(name+'.out'),
                     stderr=work/'logs'/(name+'.err'), cwd=cwd,
                     environment=env or environment, timeout=timeout,
                     stream_limit=stream_limit)
        phases.append({'name': name, **result})
        write(work/'phases.json', phases)
        require(result['exit_code'] == 0, f'{name} failed: inspect its retained log')
        if check_output:
            for path, _ in writable:
                regular_inventory(path)

    tool = [(paths['source_toolchain'], '/toolchain')]
    canonical = [(paths['canonical_library'], '/canonical')]
    (work/'challenge-src/read-control').write_text('frozen\n')
    phase('isolation-controls', ['/usr/bin/python3', '-c', '''
import os,pathlib,socket
status=dict(line.split(':',1) for line in pathlib.Path('/proc/self/status').read_text().splitlines() if ':' in line)
assert os.getuid()!=0
assert status['CapEff'].strip()=='0000000000000000'
assert status['NoNewPrivs'].strip()=='1'
assert status['Seccomp'].strip()=='2'
assert socket.if_nameindex()==[(1,'lo')]
assert not pathlib.Path('/var/run/docker.sock').exists()
assert not pathlib.Path('/home/niels').exists()
assert pathlib.Path('/frozen/read-control').read_text()=='frozen\\n'
for path in ['/frozen/mutation','/etc/qrh-mutation']:
    try:pathlib.Path(path).write_text('forbidden')
    except OSError:pass
    else:raise RuntimeError('protected write permitted')
pathlib.Path('/scratch/write-control').write_text('permitted')
print('isolation-controls-pass')
'''], [(work/'challenge-src', '/frozen')], [(work/'scratch', '/scratch')])
    require((work/'logs/isolation-controls.out').read_text().strip() ==
            'isolation-controls-pass', 'Isolation control transcript differs')
    (work/'challenge-src/read-control').unlink()
    (work/'challenge-src/Challenge.lean').write_bytes((HERE/pins['challenge_file']).read_bytes())
    phase('challenge-compile', ['/toolchain/bin/lean', '-R', '/src', '-o',
          '/build-lib/Challenge.olean', 'Challenge.lean'],
          tool+canonical+[(work/'challenge-src', '/src')], [(work/'challenge-lib', '/build-lib')],
          cwd='/src', env={**environment, 'LEAN_PATH': '/build-lib:/canonical'})
    phase('challenge-export', ['/exporter/lean4export', 'Challenge', '--', *targets],
          tool+canonical+[(paths['exporter'], '/exporter'), (work/'challenge-lib', '/build-lib')],
          env={**environment, 'LEAN_PATH': '/build-lib:/canonical'},
          output=work/'exports/Challenge.export', stream_limit=16*1024**3)
    challenge_hash = sha(work/'exports/Challenge.export')

    # Candidate input is read as bytes only after the canonical export is fixed.
    for source, expected in pins['candidate_sources'].items():
        source_path = Path(source)
        require(not source_path.is_absolute() and '..' not in source_path.parts,
                'Unsafe candidate path')
        original = real_path(paths['candidate_checkout']/source)
        require(sha(original) == expected['sha256'], 'Candidate source checksum differs')
        destination = work/'candidate-src'/expected['destination']
        require(destination.is_relative_to(work/'candidate-src') and
                '..' not in Path(expected['destination']).parts, 'Unsafe source destination')
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(original.read_bytes())
    deps = [(paths['candidate_dependencies'], '/dependencies')]
    # Lean resolves each package prefix in one search-path directory. Rebuilt
    # modules share a private copy of that prefix's approved dependencies.
    for prefix in sorted({module.split('.')[0] for module in pins['build_order']}):
        require(prefix.isidentifier(), 'Unsafe package prefix')
        dependency = paths['candidate_dependencies']/prefix
        if dependency.is_dir():
            shutil.copytree(dependency, work/'candidate-lib'/prefix)
    for module in pins['build_order']:
        require(all(part.isidentifier() for part in module.split('.')), 'Unsafe module name')
        relative = module.replace('.', '/')
        (work/'candidate-lib'/relative).parent.mkdir(parents=True, exist_ok=True)
        phase('compile-'+module, ['/toolchain/bin/lean', '-j1', '-DautoImplicit=false',
              '-DwarningAsError=false', '-R', '/src', '-o', '/build-lib/'+relative+'.olean',
              relative+'.lean'], tool+deps+[(work/'candidate-src', '/src')],
              [(work/'candidate-lib', '/build-lib')], cwd='/src',
              env={**environment, 'LEAN_PATH': '/build-lib:/dependencies'}, check_output=False)
    regular_inventory(work/'candidate-lib')
    phase('solution-export', ['/exporter/lean4export', 'Solution', '--', *targets],
          tool+deps+[(paths['exporter'], '/exporter'), (work/'candidate-lib', '/build-lib')],
          env={**environment, 'LEAN_PATH': '/build-lib:/dependencies'},
          output=work/'exports/Solution.export', stream_limit=16*1024**3)
    phase('judge', ['/judge/bin/lake', 'comparator', '--inadvisably-no-sandbox',
          '--config', '/config/comparator.json', '--challenge-from-export',
          '/exports/Challenge.export', '--solution-from-export', '/exports/Solution.export'],
          [(paths['judge_toolchain'], '/judge'), (work/'exports', '/exports'),
           (work/'config', '/config')], [(work/'scratch', '/scratch')], cwd='/scratch',
          env={**environment, 'PATH': '/judge/bin:/usr/bin:/bin'}, timeout=7200)
    transcript = (work/'logs/judge.out').read_text()+(work/'logs/judge.err').read_text()
    require('Your solution is okay!' in transcript and all(
        name+' kernel accepts the solution' in transcript for name in KERNELS),
        'Incomplete independent checker acceptance')
    require(sha(work/'exports/Challenge.export') == challenge_hash, 'Frozen challenge changed')
    for name in ['source_toolchain', 'judge_toolchain', 'exporter', 'canonical_library',
                 'candidate_dependencies']:
        require(inventory(name, paths[name]) == pins['inventories'][name],
                f'{name} changed during replay')
    artifacts = {}
    for directory in ['logs', 'challenge-src', 'candidate-src', 'config', 'exports']:
        artifacts.update({directory+'/'+key: value for key, value in
                          regular_inventory(work/directory).items()})
    write(work/'result.json', {'schema_version': 1, 'status': 'PASS',
          'verified_at': datetime.datetime.now(datetime.timezone.utc).isoformat(),
          'reviewed_pr_head': pins['head_sha'], 'theta_exact': pins['theta_exact'],
          'source_repository': pins['repository'], 'result_id': pins['result_id'],
          'targets': pins['targets'], 'allowed_axioms': AXIOMS, 'kernels': KERNELS,
          'source_compiler': '4.34.1', 'judge_toolchain': '4.35.0-rc2',
          'judge_exit_code': 0, 'image': pins['image'],
          'driver_sha256': sha(__file__), 'sandbox_sha256': sha(HERE/'sandbox.py'),
          'pins_sha256': sha(args.pins), 'controls_sha256': pins['controls_sha256'],
          'challenge_exported_before_candidate_execution': True,
          'receipt_outside_candidate': True, 'isolation': 'offline Docker',
          'official_flag': '--inadvisably-no-sandbox', 'artifacts': artifacts})


if __name__ == '__main__':
    main()
