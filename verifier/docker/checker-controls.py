import argparse,datetime,hashlib,json,pathlib,sys
parser=argparse.ArgumentParser()
parser.add_argument('--runtime',type=pathlib.Path,required=True)
parser.add_argument('--work',type=pathlib.Path,required=True)
args=parser.parse_args()
ROOT=args.runtime.resolve()
HERE=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from sandbox import run
sys.path.insert(0,str(ROOT/'palomar'))
from scripts.verify_submission import primitive_targets,comparator_export_targets,ill_typed_export
image=(ROOT/'docker-image-id.txt').read_text().strip(); toolchain=ROOT/'lean-4.35.0-rc2-linux'
work=args.work.resolve(); work.mkdir()
for n in ['src','lib','exports','logs','config','scratch']:(work/n).mkdir()
config={'challenge_module':'PalomarPreflightChallenge','solution_module':'PalomarPreflightSolution',
 'theorem_names':['palomar_preflight'],'definition_names':[],
 'permitted_axioms':['Classical.choice','Quot.sound','propext'],
 'external_kernels':{'nanoda':['/judge-toolchain/bin/nanoda_bin'],'con-ron':['/judge-toolchain/bin/con-ron','--jobs=4']}}
(work/'config/comparator.json').write_text(json.dumps(config,indent=2)+'\n')
targets=comparator_export_targets(config,primitive_targets(toolchain))
modules={'PalomarPreflightChallenge':'theorem palomar_preflight : True := trivial\n',
 'PalomarPreflightSolution':'theorem palomar_preflight : True := trivial\n',
 'PalomarPreflightWrong':'theorem palomar_preflight : True ∧ True := ⟨trivial, trivial⟩\n'}
env={'PATH':'/judge-toolchain/bin:/usr/bin:/bin','HOME':'/tmp','TMPDIR':'/tmp','LANG':'C.UTF-8','LEAN_PATH':'/build-lib','LEAN_ABORT_ON_PANIC':'1'}
for name,text in modules.items():
 (work/'src'/f'{name}.lean').write_text(text)
 r=run(image=image,command=['/judge-toolchain/bin/lean','-R','/src','-o',f'/build-lib/{name}.olean',f'{name}.lean'],
  readonly=[(toolchain,'/judge-toolchain'),(work/'src','/src')],writable=[(work/'lib','/build-lib')],
  stdout=work/'logs'/f'compile-{name}.out',stderr=work/'logs'/f'compile-{name}.err',cwd='/src',environment=env)
 assert r['exit_code']==0,r
 r=run(image=image,command=['/judge-toolchain/bin/leanexport',name,'--',*targets],
  readonly=[(toolchain,'/judge-toolchain'),(work/'lib','/build-lib')],writable=[],
  stdout=work/'exports'/f'{name}.export',stderr=work/'logs'/f'export-{name}.err',cwd='/tmp',environment=env,stream_limit=128*1024**2)
 assert r['exit_code']==0,r
(work/'exports/PalomarPreflightIllTyped.export').write_bytes(ill_typed_export(work/'exports/PalomarPreflightSolution.export','palomar_preflight'))
cases=[]
for name,code,message in [('PalomarPreflightSolution',0,'Your solution is okay!'),('PalomarPreflightWrong',1,'Challenge and solution theorem statement do not match'),('PalomarPreflightIllTyped',1,'Lean default kernel rejected the solution')]:
 scratch=work/'scratch'/name;scratch.mkdir()
 r=run(image=image,command=['/judge-toolchain/bin/lake','comparator','--inadvisably-no-sandbox','--config','/config/comparator.json',
   '--challenge-from-export','/exports/PalomarPreflightChallenge.export','--solution-from-export',f'/exports/{name}.export'],
  readonly=[(toolchain,'/judge-toolchain'),(work/'exports','/exports'),(work/'config','/config')],writable=[(scratch,'/scratch')],
  stdout=work/'logs'/f'judge-{name}.out',stderr=work/'logs'/f'judge-{name}.err',cwd='/scratch',environment=env)
 log=(work/'logs'/f'judge-{name}.out').read_text()+(work/'logs'/f'judge-{name}.err').read_text()
 assert r['exit_code']==code,(r,log)
 assert message in log,(message,log)
 if code==0:
  for kernel in ['Lean default','nanoda','con-ron']:assert f'{kernel} kernel accepts the solution' in log,log
 cases.append({'name':name,'expected_exit_code':code,'result':r,'message':message})
report={'status':'PASS','kind':'fresh-docker-official-checker-controls','completed_at':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'image':image,'driver_sha256':hashlib.sha256(pathlib.Path(__file__).read_bytes()).hexdigest(),
 'sandbox_driver_sha256':hashlib.sha256((HERE/'sandbox.py').read_bytes()).hexdigest(),
 'official_flag':'--inadvisably-no-sandbox','isolation':'Docker outer sandbox; official builtin bubblewrap disabled','cases':cases}
(work/'control-results.json').write_text(json.dumps(report,indent=2)+'\n');print(json.dumps(report,indent=2))
