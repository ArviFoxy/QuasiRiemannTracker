import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import {
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  readFileSync,
  rmSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
const entrypoint = fileURLToPath(
  new URL("../verifier/actions/prepare.mjs", import.meta.url),
);
test("algebraic bounds retain their local verification profile", (t) => {
  const cwd = mkdtempSync(join(tmpdir(), "qrh-prepare-"));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  mkdirSync(join(cwd, "verification-context"));
  const expected = {
    repository: "GTimG/QuasiRiemannTracker",
    number: 15,
    head_sha: "a".repeat(40),
    result_id: "algebraic-bound",
    theta_exact: "sqrt(3)/2",
  };
  writeFileSync(
    join(cwd, "verification-context/context.json"),
    JSON.stringify({ expected }),
  );
  const child = spawnSync(process.execPath, [entrypoint], {
    cwd,
    encoding: "utf8",
    timeout: 10000,
    env: { PATH: "/nonexistent" },
  });
  assert.ifError(child.error);
  assert.equal(child.status, 1);
  const attempt = JSON.parse(
    readFileSync(join(cwd, "verification/attempt.json"), "utf8"),
  );
  assert.equal(attempt.status, "infrastructure-blocked");
  assert.equal(attempt.theta_exact, expected.theta_exact);
  assert.match(attempt.reason, /requires an algebraic checking profile/);
});
