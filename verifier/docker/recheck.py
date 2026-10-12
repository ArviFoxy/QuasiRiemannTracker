#!/usr/bin/env python3
"""Check a new PR head whose pinned proof sources and tools are unchanged.

Preserve the original source-build receipt, authenticate both exported proofs,
and rerun Comparator and all three kernels against the new reviewed head.
"""
from pathlib import Path
import argparse
import datetime
import json
import shutil
import subprocess
from replay import AXIOMS, KERNELS, HERE, inventory, sha, write
from sandbox import run, real_path, regular_inventory, require

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--previous', type=Path, required=True)
parser.add_argument('--previous-pins', type=Path, required=True)
parser.add_argument('--pins', type=Path, required=True)
parser.add_argument('--profile', type=Path, required=True)
parser.add_argument('--work', type=Path, required=True)
args = parser.parse_args()
old = json.loads(args.previous_pins.read_text())
new = json.loads(args.pins.read_text())
before, after = dict(old), dict(new)
before.pop('head_sha'); after.pop('head_sha')
require(before == after, 'Head recheck requires identical source, target and tool pins')
report = json.loads((args.previous/'result.json').read_text())
require('source_replay' not in report and report['status'] == 'PASS' and
        report['pins_sha256'] == sha(args.previous_pins) and
        report['reviewed_pr_head'] == old['head_sha'] and
        report['driver_sha256'] == sha(HERE/'replay.py') and
        report['sandbox_sha256'] == sha(HERE/'sandbox.py'), 'Original source replay differs')
profile = json.loads(args.profile.read_text())
checkout = real_path(profile['candidate_checkout'])
require(subprocess.check_output(['git', '-C', str(checkout), 'rev-parse', 'HEAD'],
                                text=True).strip() == new['head_sha'], 'New checkout head differs')
for name, source in new['candidate_sources'].items():
    path = Path(name)
    require(not path.is_absolute() and '..' not in path.parts, 'Unsafe proof source path')
    require(sha(real_path(checkout/path)) == source['sha256'], 'Proof source changed')
    import hashlib
    committed = subprocess.check_output(['git', '-C', str(checkout), 'show', new['head_sha']+':'+name])
    require(hashlib.sha256(committed).hexdigest() == source['sha256'], 'Committed proof source changed')
for name in ['source_toolchain', 'judge_toolchain', 'exporter', 'canonical_library', 'candidate_dependencies']:
    require(inventory(name, real_path(profile[name])) == new['inventories'][name], 'Pinned input changed')
for directory in ['logs', 'challenge-src', 'candidate-src', 'config', 'exports']:
    actual = regular_inventory(args.previous/directory)
    expected = {name[len(directory)+1:]: value for name, value in report['artifacts'].items()
                if name.startswith(directory+'/')}
    require(actual == expected, 'Original source replay artifacts changed')
args.work.mkdir()
for directory in ['logs', 'challenge-src', 'candidate-src', 'config']:
    shutil.copytree(args.previous/directory, args.work/directory)
(args.work/'original-source-replay').mkdir()
for source, dest in [(args.previous/'result.json', 'result.json'),
                     (args.previous/'phases.json', 'phases.json'),
                     (args.previous_pins, 'pins.json'),
                     (args.previous/'logs/judge.out', 'judge.out'),
                     (args.previous/'logs/judge.err', 'judge.err')]:
    shutil.copyfile(source, args.work/'original-source-replay'/dest)
# Fresh supervisor output paths are required by the sandbox launcher.
for name in ['judge.out', 'judge.err']:
    (args.work/'logs'/name).unlink()
(args.work/'scratch').mkdir()
toolchain = real_path(profile['judge_toolchain'])
result = run(image=new['image'],
    command=['/judge/bin/lake', 'comparator', '--inadvisably-no-sandbox', '--config',
             '/config/comparator.json', '--challenge-from-export', '/exports/Challenge.export',
             '--solution-from-export', '/exports/Solution.export'],
    readonly=[(toolchain, '/judge'), (args.previous/'exports', '/exports'), (args.work/'config', '/config')],
    writable=[(args.work/'scratch', '/scratch')], stdout=args.work/'logs/judge.out',
    stderr=args.work/'logs/judge.err', cwd='/scratch', timeout=7200,
    environment={'PATH': '/judge/bin:/usr/bin:/bin', 'HOME': '/tmp', 'TMPDIR': '/tmp',
                 'LANG': 'C.UTF-8', 'LEAN_ABORT_ON_PANIC': '1'})
transcript = (args.work/'logs/judge.out').read_text()+(args.work/'logs/judge.err').read_text()
require(result['exit_code'] == 0 and 'Your solution is okay!' in transcript and
        all(name+' kernel accepts the solution' in transcript for name in KERNELS), 'Fresh checker acceptance required')
require(regular_inventory(args.previous/'exports') == {
    key[len('exports/'):]: value for key, value in report['artifacts'].items() if key.startswith('exports/')},
    'Frozen proof streams changed')
require(inventory('judge_toolchain', toolchain) == new['inventories']['judge_toolchain'], 'Checker tools changed')
regular_inventory(args.work/'scratch')
phases = json.loads((args.previous/'phases.json').read_text())
require(phases[-1]['name'] == 'judge', 'Original checker phase missing')
phases[-1] = {'name': 'judge', **result}
write(args.work/'phases.json', phases)
report.update(reviewed_pr_head=new['head_sha'], pins_sha256=sha(args.pins),
    verified_at=datetime.datetime.now(datetime.timezone.utc).isoformat(),
    recheck_driver_sha256=sha(__file__), source_replay={
        'head_sha': old['head_sha'], 'receipt_sha256': sha(args.previous/'result.json'),
        'pins_sha256': sha(args.previous_pins)})
for name in ['judge.out', 'judge.err']:
    report['artifacts']['logs/'+name] = sha(args.work/'logs'/name)
write(args.work/'result.json', report)
