from pathlib import Path
import concurrent.futures,json,subprocess,time
root=Path('/');graph=json.loads(Path('/controller/graph.json').read_text())
done=set();pending=set(graph);active={};failed=[];started=time.time()
def compile_one(module):
 relative=module.replace('.','/');out=Path('/build')/(relative+'.olean');out.parent.mkdir(parents=True,exist_ok=True)
 with (Path('/logs')/(module+'.log')).open('w') as log:
  return subprocess.run(['/toolchain/bin/lean','-j1'] + (['-DautoImplicit=false'] if module.startswith(('OAI.', 'QRH.', 'Mathlib.', 'RellichKondrachov.', 'MathlibExtensions.', 'PrimeNumberTheoremAnd.')) else []) + (['-DmaxSynthPendingDepth=3'] if module.startswith('Mathlib.') else []) + ['-DwarningAsError=false','-R','/source','-o',str(out),relative+'.lean'],cwd='/source',stdout=log,stderr=subprocess.STDOUT,timeout=1800).returncode
with concurrent.futures.ThreadPoolExecutor(max_workers=8) as pool:
 while pending or active:
  for module in sorted(pending):
   if len(active)>=8 or failed:break
   if any(dep in graph and dep not in done for dep in graph[module]):continue
   pending.remove(module);active[pool.submit(compile_one,module)]=module
  if not active:break
  ready,_=concurrent.futures.wait(active,return_when=concurrent.futures.FIRST_COMPLETED)
  for future in ready:
   module=active.pop(future)
   try:code=future.result()
   except Exception as error:code=1;print(type(error).__name__,str(error),flush=True)
   if code:failed.append(module)
   else:done.add(module)
  print(json.dumps({'compiled':len(done),'total':len(graph),'failed':failed,'pending':len(pending),'seconds':round(time.time()-started,1)}),flush=True)
if failed or pending:raise SystemExit(1)
