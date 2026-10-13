import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
test("parallel compilation waits for dependencies and isolates published outputs", () => {
  const result = execFileSync(
    "python3",
    [
      "-c",
      String.raw`
from verifier.standard.compile import compile_modules, publish_module
from pathlib import Path
from tempfile import TemporaryDirectory
from threading import Barrier, Lock
barrier=Barrier(2);done=set();lock=Lock()
def compile(name, threads):
    if name in ['First', 'Second']: assert threads==1
    else: assert threads==2
    if name in ['First', 'Second']: barrier.wait(timeout=5)
    if name=='Main': assert done=={'First','Second'}
    with lock: done.add(name)
compile_modules(['First','Second','Main'], {'First':[], 'Second':[], 'Main':['First','Second']},compile,jobs=2)
assert done=={'First','Second','Main'}
for graph in [{'First':['Missing']}, {'First':['First']}]:
    try: compile_modules(['First'],graph,compile,jobs=1)
    except ValueError: pass
    else: raise AssertionError('invalid dependency graph accepted')
with TemporaryDirectory() as temporary:
    root=Path(temporary);out=root/'module.olean';out.write_text('compiled')
    Path(str(out)+'.private').write_text('private')
    destination=root/'shared/Example.olean'
    publish_module(out,destination)
    assert destination.read_text()=='compiled'
    assert Path(str(destination)+'.private').read_text()=='private'
    assert destination.stat().st_mode & 0o222==0
    out.unlink();out.symlink_to(destination)
    try: publish_module(out,root/'shared/Other.olean')
    except ValueError: pass
    else: raise AssertionError('symlink output accepted')
print('PASS')
`,
    ],
    { encoding: "utf8" },
  );
  assert.match(result, /PASS/);
});
