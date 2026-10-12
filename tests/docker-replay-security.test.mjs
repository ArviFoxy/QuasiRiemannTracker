import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import test from "node:test";

test("Docker replay rejects unsafe mounts and output artifacts before use", () => {
  const result = spawnSync("python3", ["tests/docker_replay_security.py"], {
    encoding: "utf8",
    env: { ...process.env, PYTHONDONTWRITEBYTECODE: "1" },
  });
  assert.equal(result.status, 0, result.stdout + result.stderr);
});
