import test from "node:test";
import assert from "node:assert/strict";
import {
  maintenancePlan,
  maintenancePaths,
} from "../verifier/pr-maintenance.mjs";
import {
  catalogueProofRecords,
  proofRevision,
} from "../core/catalogue-revisions.mjs";
import { catalogue as fixtureCatalogue } from "./fixtures/catalogue.mjs";
import { boundLabel } from "../core/catalogue.mjs";
const catalogue = fixtureCatalogue();
function fixture(files = []) {
  const base = {};
  for (const r of catalogueProofRecords(catalogue)) {
    base[`proofs/${proofRevision(r)}/metadata.json`] = structuredClone(r);
    if (r.status === "framework-verified")
      base[`public/${r.certificate_url}`] = {
        schema_version: 1,
        result_id: proofRevision(r),
        theta_exact: boundLabel(r),
        verified_at: r.first_verified_at,
        source_repository: r.repository,
        source_commit: r.source_commit,
        report_sha256: "d".repeat(64),
        report_url:
          "https://github.com/example/proofs/actions/runs/123/attempts/1",
        kernels: ["Lean default", "nanoda", "con-ron"],
      };
  }
  const head = structuredClone(base);
  head["submissions/fixture-baseline/src/Candidate/Main.lean"] = "theorem";
  head["submissions/fixture-improvement/src/Candidate/Main.lean"] = "theorem";
  const read = (side, name) =>
    Object.hasOwn(side === "base" ? base : head, name)
      ? JSON.stringify((side === "base" ? base : head)[name])
      : null;
  const list = (side, prefix) =>
    Object.keys(side === "base" ? base : head).filter((p) =>
      p.startsWith(prefix),
    );
  return { files, base, head, read, list };
}
const modified = (filename) => ({ filename, status: "modified" });
test("website-only maintenance needs no proof or catalogue reads", () => {
  assert.equal(maintenancePaths([modified("src/App.tsx")]), false);
  assert.equal(
    maintenancePaths([
      modified("public/certificates/fixture-improvement.json"),
    ]),
    true,
  );
});
test("editing two existing proofs schedules both exact catalogue bounds", () => {
  const data = fixture([
    modified("submissions/fixture-baseline/src/Candidate/Main.lean"),
    modified("submissions/fixture-improvement/src/Candidate/Main.lean"),
    modified("src/App.tsx"),
  ]);
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "fixture-baseline", theta_exact: "7/8" },
    { result_id: "fixture-improvement", theta_exact: "8749/10000" },
  ]);
});
test("proof metadata attribution edits validate without rerunning unchanged proofs", () => {
  const data = fixture([modified("proofs/fixture-baseline/metadata.json")]);
  data.head["proofs/fixture-baseline/metadata.json"].authors[0].name =
    "Corrected attribution";
  assert.deepEqual(maintenancePlan(data), []);
});
test("changing a proof metadata bound alone fails for its mismatched verification record", () => {
  const data = fixture([modified("proofs/fixture-baseline/metadata.json")]);
  data.head["proofs/fixture-baseline/metadata.json"].theta = {
    numerator: "3",
    denominator: "2",
  };
  assert.throws(
    () => maintenancePlan(data),
    /Verification record differs from catalogue: fixture-baseline/,
  );
});
test("changing the bound and certificate together still requires kernel verification", () => {
  const data = fixture([
    modified("proofs/fixture-baseline/metadata.json"),
    modified("public/certificates/fixture-baseline.json"),
  ]);
  data.head["proofs/fixture-baseline/metadata.json"].theta = {
    numerator: "3",
    denominator: "2",
  };
  data.head["public/certificates/fixture-baseline.json"].theta_exact = "3/2";
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "fixture-baseline", theta_exact: "3/2" },
  ]);
});
test("changing certificate report provenance requires proof verification", () => {
  const data = fixture([modified("public/certificates/fixture-baseline.json")]);
  data.head["public/certificates/fixture-baseline.json"].report_sha256 =
    "e".repeat(64);
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "fixture-baseline", theta_exact: "7/8" },
  ]);
});
test("an invalid algebraic enclosure fails exact interval validation", () => {
  const data = fixture([modified("proofs/fixture-algebraic/metadata.json")]);
  const r = data.head["proofs/fixture-algebraic/metadata.json"];
  r.bound_interval.lower = r.bound_interval.upper;
  assert.throws(() => maintenancePlan(data), /Invalid certified enclosure/);
});
test("a malformed rational fails normalization", () => {
  const data = fixture([modified("proofs/fixture-baseline/metadata.json")]);
  data.head["proofs/fixture-baseline/metadata.json"].theta = {
    numerator: "2",
    denominator: "2",
  };
  assert.throws(() => maintenancePlan(data), /normalized/);
});
test("deleting one module rechecks the remaining submission", () => {
  const data = fixture([
    {
      filename: "submissions/fixture-improvement/src/Candidate/Helper.lean",
      status: "removed",
    },
  ]);
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "fixture-improvement", theta_exact: "8749/10000" },
  ]);
});
test("removing an archived proof validates metadata and retained pinned sources", () => {
  const data = fixture([
    { filename: "proofs/retired/Solution.lean", status: "removed" },
  ]);
  assert.deepEqual(maintenancePlan(data), []);
});
test("renaming away a required module rechecks the remaining submission", () => {
  const data = fixture([
    {
      filename: "archive/Main.txt",
      previous_filename:
        "submissions/fixture-improvement/src/Candidate/Main.lean",
      status: "renamed",
    },
  ]);
  delete data.head["submissions/fixture-improvement/src/Candidate/Main.lean"];
  data.head["submissions/fixture-improvement/src/Candidate/Helper.lean"] =
    "helper";
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "fixture-improvement", theta_exact: "8749/10000" },
  ]);
});
test("new proof source requires known exact-bound metadata", () => {
  const data = fixture([
    modified("submissions/unknown-proof/src/Candidate/Main.lean"),
  ]);
  data.head["submissions/unknown-proof/src/Candidate/Main.lean"] = "theorem";
  assert.throws(
    () => maintenancePlan(data),
    /Cannot determine the exact bound for unknown-proof/,
  );
});
test("proof source must use the standard submission layout", () => {
  const data = fixture([modified("proofs/fixture-improvement/Solution.lean")]);
  assert.throws(
    () => maintenancePlan(data),
    /Place maintained proof source in submissions/,
  );
});
test("generated catalogue files cannot be reintroduced to bypass proof metadata", () => {
  for (const path of ["catalogue/results.json", "public/catalogue.json"]) {
    const data = fixture([{ filename: path, status: "added" }]);
    data.head[path] = structuredClone(catalogue);
    assert.throws(
      () => maintenancePlan(data),
      /generated catalogue|generated output/i,
    );
  }
});
test("removing a required verification record fails before proof scheduling", () => {
  const data = fixture([
    {
      filename: "public/certificates/fixture-improvement.json",
      status: "removed",
    },
  ]);
  delete data.head["public/certificates/fixture-improvement.json"];
  assert.throws(() => maintenancePlan(data), /Invalid verification record/);
});

test("reformatting certificate fields preserves verification", () => {
  const data = fixture([modified("public/certificates/fixture-baseline.json")]);
  const path = "public/certificates/fixture-baseline.json";
  data.head[path] = Object.fromEntries(
    Object.entries(data.head[path]).reverse(),
  );
  assert.deepEqual(maintenancePlan(data), []);
});

test("existing admitted proof source uses the exact bound and certificate from the archive", () => {
  const data = fixture([
    modified("submissions/fixture-improvement/src/Candidate/Main.lean"),
  ]);
  const record = data.base["proofs/fixture-improvement/metadata.json"];
  const certificate = data.base["public/certificates/fixture-improvement.json"];
  for (const side of [data.base, data.head]) {
    delete side["proofs/fixture-improvement/metadata.json"];
    delete side["public/certificates/fixture-improvement.json"];
  }
  assert.deepEqual(
    maintenancePlan({
      ...data,
      admittedCatalogue: { schema_version: 1, records: [record] },
      readAdmittedCertificate: (id) =>
        id === record.id ? JSON.stringify(certificate) : null,
    }),
    [{ result_id: "fixture-improvement", theta_exact: "8749/10000" }],
  );
});

test("a metadata file cannot replace an admitted archive entry", () => {
  const data = fixture([
    { filename: "proofs/fixture-improvement/metadata.json", status: "added" },
  ]);
  const admitted = data.base["proofs/fixture-improvement/metadata.json"];
  delete data.base["proofs/fixture-improvement/metadata.json"];
  assert.throws(
    () =>
      maintenancePlan({
        ...data,
        admittedCatalogue: { schema_version: 1, records: [admitted] },
      }),
    /Metadata duplicates an admitted proof/,
  );
});

test("proof metadata filenames must match the immutable revision they describe", () => {
  const data = fixture([modified("proofs/fixture-baseline/metadata.json")]);
  data.head["proofs/fixture-baseline/metadata.json"].id = "different-revision";
  assert.throws(() => maintenancePlan(data), /metadata path differs/);
});
