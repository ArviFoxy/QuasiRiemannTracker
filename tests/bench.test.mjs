import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";

test("the compile-cost benchmark keys, schedules, checks and summarizes measurements", () => {
  const run = spawnSync("python3", ["tests/bench.py"], { encoding: "utf8" });
  assert.equal(run.status, 0, run.stdout + run.stderr);
});
