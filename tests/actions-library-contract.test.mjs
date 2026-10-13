import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
test("worker setup binds new libraries while preserving read-only prepared inputs", () => {
  const result = spawnSync(
    "python3",
    [
      "-c",
      `
from pathlib import Path
import hashlib,json,stat,sys,tempfile
sys.path.insert(0, 'verifier/actions')
from library_contract import bind_libraries
with tempfile.TemporaryDirectory() as temporary:
    prepared=Path(temporary)
    (prepared/'libraries.json').write_text('{}')
    (prepared/'contract.json').write_text(json.dumps({'head_sha':'a'*40,'source_files':{'source':'hash'},'library_inventory_sha256':'old'}))
    for p in prepared.iterdir(): p.chmod(0o444)
    inventory={'/libraries/Mathlib.olean':'b'*64}
    bind_libraries(prepared,inventory)
    contract=json.loads((prepared/'contract.json').read_text())
    assert contract['head_sha']=='a'*40 and contract['source_files']=={'source':'hash'}
    assert contract['library_inventory_sha256']==hashlib.sha256((prepared/'libraries.json').read_bytes()).hexdigest()
    assert json.loads((prepared/'libraries.json').read_text())==inventory
    assert all(stat.S_IMODE(p.stat().st_mode)==0o444 for p in prepared.iterdir())
`,
    ],
    { encoding: "utf8" },
  );
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stderr);
});
