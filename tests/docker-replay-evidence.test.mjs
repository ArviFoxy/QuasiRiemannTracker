import assert from "node:assert/strict";
import { createHash } from "node:crypto";
import {
  cpSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { dirname, join } from "node:path";
import test from "node:test";
import { validateAdmission } from "../verifier/pr-evidence.mjs";
import { validateDockerCatalogue } from "../core/docker-replay-evidence.mjs";

const sha = (bytes) => createHash("sha256").update(bytes).digest("hex");
const read = (path) => JSON.parse(readFileSync(path, "utf8"));
const admissions = read("verifier/pr-admissions.json").admissions;
function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), "qrh-docker-evidence-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const entry = structuredClone(admissions.find((entry) => entry.number === 5));
  assert.ok(entry, "classical independent receipt must be archived");
  for (const path of ["verifier/docker", entry.pin.directory]) {
    mkdirSync(dirname(join(root, path)), { recursive: true });
    cpSync(path, join(root, path), { recursive: true });
  }
  const evidence = join(root, entry.pin.directory);
  const report = read(join(evidence, "result.json"));
  const collection = read(join(evidence, "collection.json"));
  const inputs = read(join(root, "verifier/docker/classical-pins.json"));
  const save = (name, value) => {
    writeFileSync(join(evidence, name), JSON.stringify(value, null, 2) + "\n");
    collection.files[name] = sha(readFileSync(join(evidence, name)));
  };
  const resign = () => {
    save("result.json", report);
    writeFileSync(
      join(evidence, "collection.json"),
      JSON.stringify(collection),
    );
    entry.pin.receipt_sha256 = collection.files["result.json"];
    entry.pin.collection_sha256 = sha(
      readFileSync(join(evidence, "collection.json")),
    );
    writeFileSync(
      join(root, "verifier/pr-admissions.json"),
      JSON.stringify({ schema_version: 1, admissions: [entry] }),
    );
  };
  resign();
  const check = () =>
    validateAdmission(
      root,
      Object.fromEntries(
        ["repository", "number", "head_sha", "result_id", "theta_exact"].map(
          (key) => [key, entry[key]],
        ),
      ),
    );
  return {
    root,
    entry,
    evidence,
    report,
    collection,
    inputs,
    save,
    resign,
    check,
  };
}

test("archived independent Docker receipts admit their exact heads and bounds", () => {
  const entries = admissions.filter((entry) =>
    entry.pin.replay_profile.startsWith("docker-"),
  );
  assert.ok(entries.some((entry) => entry.theta_exact === "1/1"));
  for (const entry of entries) {
    const expected = Object.fromEntries(
      ["repository", "number", "head_sha", "result_id", "theta_exact"].map(
        (key) => [key, entry[key]],
      ),
    );
    assert.equal(validateAdmission(process.cwd(), expected).status, "PASS");
  }
});

for (const [name, change, reason] of [
  [
    "an unchecked target",
    (report) => {
      report.targets = ["QRH.unchecked"];
    },
    /target scope differs/,
  ],
  [
    "a different source head",
    (report) => {
      report.reviewed_pr_head = "a".repeat(40);
    },
    /source head or repository differs/,
  ],
  [
    "an extra axiom",
    (report) => {
      report.allowed_axioms.push("sorryAx");
    },
    /kernel or axiom scope differs/,
  ],
  [
    "candidate access to the receipt",
    (report) => {
      report.receipt_outside_candidate = false;
    },
    /isolation or challenge ordering differs/,
  ],
])
  test(`rejects ${name} after collection hashes are updated`, (t) => {
    const f = fixture(t);
    change(f.report);
    f.resign();
    assert.throws(f.check, reason);
  });

test("a missing checker phase fails for its execution gap", (t) => {
  const f = fixture(t),
    phases = read(join(f.evidence, "phases.json"));
  phases.pop();
  f.save("phases.json", phases);
  f.resign();
  assert.throws(f.check, /replay phase failed or missing/);
});

test("negative checker controls require the expected rejection reason", (t) => {
  const f = fixture(t),
    controls = read(join(f.evidence, "controls/control-results.json"));
  controls.cases[1].message = "network timeout";
  f.save("controls/control-results.json", controls);
  f.inputs.controls_sha256 =
    f.collection.files["controls/control-results.json"];
  const pinsPath = join(f.root, "verifier/docker/classical-pins.json");
  writeFileSync(pinsPath, JSON.stringify(f.inputs));
  f.report.pins_sha256 = sha(readFileSync(pinsPath));
  f.report.controls_sha256 = f.inputs.controls_sha256;
  f.resign();
  assert.throws(f.check, /checker controls failed for an unexpected reason/);
});

test("catalogue publication binds the current proof bytes to the accepted source", (t) => {
  const f = fixture(t);
  for (const path of Object.keys(f.inputs.candidate_sources)) {
    mkdirSync(dirname(join(f.root, path)), { recursive: true });
    writeFileSync(join(f.root, path), "-- changed proof source\n");
  }
  assert.throws(
    () =>
      validateDockerCatalogue(f.root, {
        records: [
          {
            id: f.entry.result_id,
            status: "historical-baseline",
            theta: { numerator: "1", denominator: "1" },
          },
        ],
      }),
    /catalogue proof source differs from independent replay/,
  );
});

test("a negative control log must contain the actual statement-mismatch reason", (t) => {
  const f = fixture(t),
    name = "controls/logs/judge-PalomarPreflightWrong.out";
  writeFileSync(join(f.evidence, name), "network timeout\n");
  f.collection.files[name] = sha(readFileSync(join(f.evidence, name)));
  const errorName = "controls/logs/judge-PalomarPreflightWrong.err";
  writeFileSync(join(f.evidence, errorName), "transport failed\n");
  f.collection.files[errorName] = sha(
    readFileSync(join(f.evidence, errorName)),
  );
  f.resign();
  assert.throws(
    f.check,
    /checker control transcript has the wrong rejection reason/,
  );
});

function modelHeadRecheck(f) {
  // Protocol fixture: retain a real source replay and model a later checker
  // receipt. This test does not execute or claim a new mathematical check.
  mkdirSync(join(f.evidence, "original-source-replay"));
  for (const name of ["result.json", "phases.json"])
    f.save("original-source-replay/" + name, read(join(f.evidence, name)));
  f.save("original-source-replay/pins.json", f.inputs);
  for (const name of ["judge.out", "judge.err"]) {
    const bytes = readFileSync(join(f.evidence, "logs", name));
    writeFileSync(join(f.evidence, "original-source-replay", name), bytes);
    f.collection.files["original-source-replay/" + name] = sha(bytes);
  }
  f.report.source_replay = {
    head_sha: f.inputs.head_sha,
    receipt_sha256: f.collection.files["original-source-replay/result.json"],
    pins_sha256: f.collection.files["original-source-replay/pins.json"],
  };
  f.inputs.head_sha =
    f.report.reviewed_pr_head =
    f.entry.head_sha =
      "b".repeat(40);
  f.entry.contribution.source_commit = f.entry.head_sha;
  const pinsPath = join(f.root, "verifier/docker/classical-pins.json");
  writeFileSync(pinsPath, JSON.stringify(f.inputs, null, 2) + "\n");
  f.report.pins_sha256 = sha(readFileSync(pinsPath));
  f.report.recheck_driver_sha256 = sha(
    readFileSync(join(f.root, "verifier/docker/recheck.py")),
  );
  f.resign();
}

test("head rechecks preserve the authenticated source replay", (t) => {
  const f = fixture(t);
  modelHeadRecheck(f);
  assert.equal(f.check().status, "PASS");
  f.inputs.candidate_sources[
    Object.keys(f.inputs.candidate_sources)[0]
  ].sha256 = "c".repeat(64);
  const path = join(f.root, "verifier/docker/classical-pins.json");
  writeFileSync(path, JSON.stringify(f.inputs));
  f.report.pins_sha256 = sha(readFileSync(path));
  f.resign();
  assert.throws(f.check, /head recheck changed source, target or tool pins/);
});
