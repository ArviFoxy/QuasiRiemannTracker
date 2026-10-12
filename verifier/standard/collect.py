"""Collect accepted standard replay metadata; retain exports in the original run."""
from pathlib import Path
import argparse, hashlib, json, shutil
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument('--run',type=Path,required=True)
parser.add_argument('--driver',type=Path,required=True)
parser.add_argument('--out',type=Path,required=True)
a=parser.parse_args()
sha=lambda p:hashlib.file_digest(open(p,'rb'),'sha256').hexdigest()
r=json.loads((a.run/'result.json').read_text())
assert r['status']=='PASS' and r['judge_exit_code']==0
assert sha(a.driver)==r['driver_sha256']
a.out.mkdir(parents=True,exist_ok=False)
names=['result.json','contract.json','comparator.json','controls.json','tools.json','phases.json','challenge-src/Challenge.lean','solution-src/Solution.lean']
names += ['source/'+name for name in r['source_files']]
names += [str(p.relative_to(a.run)) for p in sorted((a.run/'logs').glob('*.log'))]
for name in names:
 src=a.run/name
 assert not src.is_symlink() and src.is_file()
 if name.startswith('source/'): assert sha(src)==r['source_files'][name.removeprefix('source/')]
 elif name!='result.json': assert sha(src)==r['artifacts'][name]
 dst=a.out/name;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(src,dst)
shutil.copyfile(a.driver,a.out/'replay.py')
collection={'schema_version':1,'kind':'standard-submission-replay','files':{str(p.relative_to(a.out)):sha(p) for p in sorted(a.out.rglob('*')) if p.is_file()}}
(a.out/'collection.json').write_text(json.dumps(collection,indent=2)+'\n')
print(json.dumps({'collection_sha256':sha(a.out/'collection.json'),'receipt_sha256':sha(a.out/'result.json'),'driver_sha256':r['driver_sha256'],'result_id':r['result_id'],'theta_exact':r['theta_exact'],'replay_profile':'standard-submission-v1'},indent=2))
