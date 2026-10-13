import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  maintenancePlan,
  maintenancePaths,
} from "../verifier/pr-maintenance.mjs";
import {
  catalogueProofRecords,
  proofRevision,
} from "../core/catalogue-revisions.mjs";
const catalogue = JSON.parse(
  readFileSync(new URL("../catalogue/results.json", import.meta.url)),
);
function fixture(files = []) {
  const base = { "catalogue/results.json": structuredClone(catalogue) };
  for (const r of catalogueProofRecords(catalogue)) {
    if (r.status === "framework-verified")
      base[`public/${r.certificate_url}`] = JSON.parse(
        readFileSync(
          new URL(`../public/${r.certificate_url}`, import.meta.url),
        ),
      );
  }
  const head = structuredClone(base);
  head["submissions/classical-euler-product/src/Candidate/Main.lean"] =
    "theorem";
  head["submissions/openai-baseline/src/Candidate/Main.lean"] = "theorem";
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
    maintenancePaths([modified("public/certificates/openai-baseline.json")]),
    true,
  );
});
test("editing two existing proofs schedules both exact catalogue bounds", () => {
  const data = fixture([
    modified("submissions/classical-euler-product/src/Candidate/Main.lean"),
    modified("submissions/openai-baseline/src/Candidate/Main.lean"),
    modified("src/App.tsx"),
  ]);
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "classical-euler-product", theta_exact: "1/1" },
    { result_id: "openai-baseline", theta_exact: "7/8" },
  ]);
});
test("catalogue attribution edits validate without rerunning unchanged proofs", () => {
  const data = fixture([modified("catalogue/results.json")]);
  data.head["catalogue/results.json"].records[0].authors[0].name =
    "Corrected attribution";
  assert.deepEqual(maintenancePlan(data), []);
});
test("changing a catalogue bound alone fails for its mismatched verification record", () => {
  const data = fixture([modified("catalogue/results.json")]);
  data.head["catalogue/results.json"].records[0].theta = {
    numerator: "3",
    denominator: "2",
  };
  assert.throws(
    () => maintenancePlan(data),
    /Verification record differs from catalogue: classical-euler-product/,
  );
});
test("changing the bound and certificate together still requires kernel verification", () => {
  const data = fixture([
    modified("catalogue/results.json"),
    modified("public/certificates/classical-euler-product.json"),
  ]);
  data.head["catalogue/results.json"].records[0].theta = {
    numerator: "3",
    denominator: "2",
  };
  data.head["public/certificates/classical-euler-product.json"].theta_exact =
    "3/2";
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "classical-euler-product", theta_exact: "3/2" },
  ]);
});
test("changing certificate report provenance requires proof verification", () => {
  const data = fixture([
    modified("public/certificates/classical-euler-product.json"),
  ]);
  data.head["public/certificates/classical-euler-product.json"].report_sha256 =
    "e".repeat(64);
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "classical-euler-product", theta_exact: "1/1" },
  ]);
});
test("an invalid algebraic enclosure fails exact interval validation", () => {
  const data = fixture([modified("catalogue/results.json")]);
  const r = data.head["catalogue/results.json"].records.find(
    (r) => r.exact_bound,
  );
  r.bound_interval.lower = r.bound_interval.upper;
  assert.throws(() => maintenancePlan(data), /Invalid certified enclosure/);
});
test("a malformed rational fails normalization", () => {
  const data = fixture([modified("catalogue/results.json")]);
  data.head["catalogue/results.json"].records[0].theta = {
    numerator: "2",
    denominator: "2",
  };
  assert.throws(() => maintenancePlan(data), /normalized/);
});
test("deleting one module rechecks the remaining submission", () => {
  const data = fixture([
    {
      filename: "submissions/openai-baseline/src/Candidate/Helper.lean",
      status: "removed",
    },
  ]);
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "openai-baseline", theta_exact: "7/8" },
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
      previous_filename: "submissions/openai-baseline/src/Candidate/Main.lean",
      status: "renamed",
    },
  ]);
  delete data.head["submissions/openai-baseline/src/Candidate/Main.lean"];
  data.head["submissions/openai-baseline/src/Candidate/Helper.lean"] = "helper";
  assert.deepEqual(maintenancePlan(data), [
    { result_id: "openai-baseline", theta_exact: "7/8" },
  ]);
});
test("new proof source requires an exact bound in catalogue data", () => {
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
  const data = fixture([modified("proofs/openai-baseline/Solution.lean")]);
  assert.throws(
    () => maintenancePlan(data),
    /Place maintained proof source in submissions/,
  );
});
test("a public catalogue edit cannot bypass the source catalogue", () => {
  const data = fixture([modified("public/catalogue.json")]);
  data.head["public/catalogue.json"] = structuredClone(catalogue);
  data.head["public/catalogue.json"].records[0].theta = {
    numerator: "3",
    denominator: "2",
  };
  assert.throws(() => maintenancePlan(data), /Published catalogue differs/);
});
test("removing a required verification record fails before proof scheduling", () => {
  const data = fixture([
    { filename: "public/certificates/openai-baseline.json", status: "removed" },
  ]);
  delete data.head["public/certificates/openai-baseline.json"];
  assert.throws(() => maintenancePlan(data), /Invalid verification record/);
});

test("reformatting certificate fields preserves verification", () => {
  const data = fixture([
    modified("public/certificates/classical-euler-product.json"),
  ]);
  const path = "public/certificates/classical-euler-product.json";
  data.head[path] = Object.fromEntries(
    Object.entries(data.head[path]).reverse(),
  );
  assert.deepEqual(maintenancePlan(data), []);
});
