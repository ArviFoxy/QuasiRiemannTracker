import test from "node:test";
import assert from "node:assert/strict";
import {
  mkdtempSync,
  mkdirSync,
  readFileSync,
  writeFileSync,
  cpSync,
  rmSync,
} from "node:fs";
import { join } from "node:path";
import { tmpdir } from "node:os";
import { createHash } from "node:crypto";
import {
  validateStandardReplay,
  validateStandardCatalogue,
} from "../core/standard-replay.mjs";
const directory = "verifier/standard/receipts/classical-first-20261012";
const hash = (b) => createHash("sha256").update(b).digest("hex");
function fixture(fn) {
  const root = mkdtempSync(join(tmpdir(), "qrh-standard-receipt-"));
  try {
    cpSync(directory, join(root, directory), { recursive: true });
    cpSync(
      "verifier/standard/tool-pins.json",
      join(root, "verifier/standard/tool-pins.json"),
    );
    const file = (name) => join(root, directory, name);
    const read = (name) => JSON.parse(readFileSync(file(name), "utf8"));
    const write = (name, data) =>
      writeFileSync(file(name), JSON.stringify(data, null, 2) + "\n");
    cpSync(
      "verifier/standard/library-pins.json",
      join(root, "verifier/standard/library-pins.json"),
    );
    const r = read("result.json");
    const pin = {
      directory,
      result_id: r.result_id,
      theta_exact: r.theta_exact,
      driver_sha256: r.driver_sha256,
    };
    const contribution = {
      repository: r.source_repository,
      source_commit: r.source_commit ?? r.reviewed_pr_head,
    };
    function seal() {
      const report = read("result.json"),
        collection = read("collection.json");
      for (const name of Object.keys(collection.files))
        if (name !== "result.json" && name !== "replay.py")
          report.artifacts[name] = hash(readFileSync(file(name)));
      write("result.json", report);
      for (const name of Object.keys(collection.files))
        collection.files[name] = hash(readFileSync(file(name)));
      write("collection.json", collection);
      pin.collection_sha256 = hash(readFileSync(file("collection.json")));
      pin.receipt_sha256 = hash(readFileSync(file("result.json")));
    }
    seal();
    fn({
      root,
      pin,
      contribution,
      file,
      read,
      write,
      seal,
      validate: () => validateStandardReplay(root, pin, contribution),
    });
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
}
test("reviewed standard receipt authenticates the recorded canonical proof", () =>
  fixture((f) => assert.equal(f.validate().status, "PASS")));
for (const [name, change, error] of [
  [
    "changed PR head",
    (r) => {
      r.reviewed_pr_head = "f".repeat(40);
    },
    /source revision differs/,
  ],
  [
    "changed bound",
    (r) => {
      r.theta_exact = "2\/1";
    },
    /exact bound differs/,
  ],
  [
    "missing kernel",
    (r) => {
      r.kernels.pop();
    },
    /kernel or axiom scope differs/,
  ],
  [
    "disabled confinement",
    (r) => {
      r.candidate_mount_preflight = "FAIL";
    },
    /isolation or challenge ordering missing/,
  ],
  [
    "unapproved checker",
    (r) => {
      r.tool_pins.judge_lean = "0".repeat(64);
    },
    /checker tool pins differ/,
  ],
])
  test(`standard receipt rejects ${name}`, () =>
    fixture((f) => {
      const r = f.read("result.json");
      change(r);
      f.write("result.json", r);
      f.seal();
      assert.throws(f.validate, error);
    }));
test("weakened statement fails the canonical comparison after hashes are updated", () =>
  fixture((f) => {
    const name = "challenge-src/Challenge.lean";
    writeFileSync(
      f.file(name),
      readFileSync(f.file(name), "utf8").replace("¬ (χ = 1 ∧ s = 1)", "True"),
    );
    const c = f.read("contract.json");
    c.generated_files["Challenge.lean"] = hash(readFileSync(f.file(name)));
    f.write("contract.json", c);
    f.seal();
    assert.throws(f.validate, /canonical challenge differs/);
  }));
test("infrastructure failure cannot stand in for ill-typed proof rejection", () =>
  fixture((f) => {
    const control = f
      .read("controls.json")
      .find((c) => c.expected === "ill-typed-proof");
    writeFileSync(
      f.file(control.log),
      "bwrap: namespace initialization failed\n",
    );
    f.seal();
    assert.throws(f.validate, /wrong proof rejection reason/);
  }));

test("catalogue verification binds the published source and first acceptance time", () =>
  fixture((f) => {
    const report = f.read("result.json"),
      contract = f.read("contract.json");
    const source = join(f.root, "submissions", report.result_id);
    cpSync(f.file("source"), source, { recursive: true });
    writeFileSync(
      join(f.root, "verifier/standard/catalogue-pins.json"),
      JSON.stringify({
        [report.result_id]: { pin: f.pin, contribution: f.contribution },
      }),
    );
    const record = {
      id: report.result_id,
      status: "framework-verified",
      first_verified_at: report.verified_at,
      repository: report.source_repository,
      source_commit: report.reviewed_pr_head,
      theta: contract.manifest.theta,
      entrypoint: contract.manifest.entrypoint,
    };
    const validate = () =>
      validateStandardCatalogue(f.root, { records: [record] });
    assert.doesNotThrow(validate);
    record.first_verified_at = "2020-01-01T00:00:00Z";
    assert.throws(validate, /catalogue verification identity differs/);
    record.first_verified_at = report.verified_at;
    writeFileSync(
      join(source, "src/Candidate/Main.lean"),
      "-- Changed after verification\n",
    );
    assert.throws(validate, /verified submission source changed/);
  }));
