#!/usr/bin/env python3
"""Collect completed maintainer evidence for review, retaining exact log bytes."""
from pathlib import Path
import argparse
import json
import shutil
from sandbox import regular_inventory, require
from replay import sha, write

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--work', type=Path, required=True)
parser.add_argument('--controls', type=Path, required=True)
parser.add_argument('--destination', type=Path, required=True)
args = parser.parse_args()
report = json.loads((args.work/'result.json').read_text())
require(report['status'] == 'PASS', 'Completed checker acceptance required')
for name in ['logs', 'challenge-src', 'config']:
    regular_inventory(args.work/name)
regular_inventory(args.controls/'logs')
args.destination.mkdir(parents=True)
for name in ['logs', 'challenge-src', 'config']:
    shutil.copytree(args.work/name, args.destination/name)
if (args.work/'original-source-replay').exists():
    regular_inventory(args.work/'original-source-replay')
    shutil.copytree(args.work/'original-source-replay', args.destination/'original-source-replay')
for name in ['result.json', 'phases.json']:
    shutil.copyfile(args.work/name, args.destination/name)
(args.destination/'controls').mkdir()
shutil.copyfile(args.controls/'control-results.json', args.destination/'controls/control-results.json')
shutil.copytree(args.controls/'logs', args.destination/'controls/logs')
shutil.copytree(args.controls/'config', args.destination/'controls/config')
write(args.destination/'collection.json', {'schema_version': 1,
      'kind': 'independent-docker-maintainer-replay',
      'files': regular_inventory(args.destination)})
print(json.dumps({'collection_sha256': sha(args.destination/'collection.json'),
                  'receipt_sha256': sha(args.destination/'result.json')}))
