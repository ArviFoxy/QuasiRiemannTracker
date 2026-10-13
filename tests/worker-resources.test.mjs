import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";

test("Lean parallelism respects affinity, ancestor quotas, memory and operator limits", () => {
  const result = spawnSync(
    "python3",
    [
      "-c",
      `
from pathlib import Path
import sys, tempfile
sys.path.insert(0, 'verifier')
from worker_resources import worker_threads, worker_capacity, GIB
with tempfile.TemporaryDirectory() as temporary:
    root = Path(temporary)
    cgroup = root/'cgroup'
    job = cgroup/'runner/job'
    job.mkdir(parents=True)
    membership = root/'membership'
    membership.write_text('0::/runner/job\\n')
    def threads(cpus=16, memory=64*GIB, env=None):
        return worker_threads(environ=env or {}, affinity=cpus, memory_bytes=memory,
                              cgroup_root=cgroup, membership=membership)
    assert threads() == 16
    def kernels(cpus=16, memory=64*GIB, env=None):
        return worker_capacity(environ=env or {}, affinity=cpus, memory_bytes=memory,
                               cgroup_root=cgroup, membership=membership)['kernel_jobs']
    assert kernels() == 3
    assert kernels(cpus=4, memory=16*GIB) == 1
    assert kernels(cpus=4, memory=16*GIB, env={'QRH_KERNEL_JOBS':'3'}) == 3
    assert kernels(env={'QRH_WORKER_THREADS':'1'}) == 1
    assert kernels(env={'QRH_KERNEL_JOBS':'1'}) == 1
    assert threads(cpus=4, memory=16*GIB) == 4
    assert threads(cpus=2, memory=7*GIB) == 2
    assert threads(cpus=8) == 8
    assert threads(memory=8*GIB) == 3
    assert threads(memory=GIB) == 1
    assert threads(env={'QRH_WORKER_THREADS':'6'}) == 6
    assert threads(env={'QRH_WORKER_THREADS':'32'}) == 16
    # A delegated job inherits constraints from the parent runner cgroup.
    (job.parent/'cpu.max').write_text('600000 100000')
    (job/'cpu.max').write_text('max 100000')
    assert threads() == 6
    (job/'cpu.max').write_text('250000 100000')
    assert threads() == 2
    (job/'cpu.max').write_text('50000 100000')
    assert threads() == 1
    (job/'cpu.max').write_text('max 100000')
    (job.parent/'cpu.max').write_text('max 100000')
    (cgroup/'memory.max').write_text(str(8*GIB))
    (job/'memory.max').write_text('max')
    assert threads() == 3
    (cgroup/'memory.max').write_text('max')
    assert threads() == 16
    for value in ['', '0', '-2', '1.5', 'abc']:
        try:
            threads(env={'QRH_WORKER_THREADS':value})
        except ValueError:
            pass
        else:
            raise AssertionError('Accepted invalid thread count: '+value)
    # Cgroup namespaces can expose only the mounted root's limit.
    membership.unlink()
    (cgroup/'cpu.max').write_text('400000 100000')
    assert threads() == 4
`,
    ],
    { encoding: "utf8" },
  );
  assert.ifError(result.error);
  assert.equal(result.status, 0, result.stderr);
});
