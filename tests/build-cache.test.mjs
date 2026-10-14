import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";

test("authenticated shared module cache rejects changed inputs and malformed archives", () => {
  const run = spawnSync("python3", ["tests/build-cache.py"], {
    encoding: "utf8",
  });
  assert.equal(run.status, 0, run.stdout + run.stderr);
});

test("proof workers upload diagnostics and then report failed verification", () => {
  const workflow = readFileSync(".github/workflows/pr-admission.yml", "utf8");
  const worker = workflow.split("  verify:\n")[1].split("  admission:\n")[0];
  assert.ok(
    worker.indexOf("Require successful worker verification") >
      worker.indexOf("actions/upload-artifact"),
  );
  assert.match(worker, /if: always\(\) && steps\.check\.outcome != 'success'/);
  assert.match(worker, /exit 1/);
});
