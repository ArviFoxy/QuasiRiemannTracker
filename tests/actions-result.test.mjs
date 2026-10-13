import test from "node:test";
import assert from "node:assert/strict";
import { verificationResult } from "../verifier/actions/result.mjs";
const expected = {
  repository: "GTimG/QuasiRiemannTracker",
  number: 15,
  head_sha: "a".repeat(40),
  result_id: "candidate-proof",
  theta_exact: "1/1",
};
const accepted = () => ({
  ...expected,
  status: "accepted",
  report: {
    status: "PASS",
    reviewed_pr_head: expected.head_sha,
    source_repository: expected.repository,
    result_id: expected.result_id,
    theta_exact: expected.theta_exact,
    judge_exit_code: 0,
    targets: ["QRH.canonical_bound"],
    kernels: ["Lean default", "nanoda", "con-ron"],
    allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
    sandbox_preflight: "PASS",
    candidate_mount_preflight: "PASS",
    challenge_exported_before_candidate_execution: true,
    receipt_outside_candidate: true,
  },
});
const forbiddenFallback = () => {
  throw Error("Fallback must not be consulted");
};
test("a successful live run passes without any registered local evidence", () => {
  const a = accepted();
  assert.equal(
    verificationResult("unused", expected, a, "success", forbiddenFallback),
    a.report,
  );
});
for (const key of [
  "head_sha",
  "result_id",
  "theta_exact",
  "number",
  "repository",
])
  test(`rejects a live report with another ${key}`, () => {
    const a = accepted();
    a[key] = "different";
    assert.throws(
      () =>
        verificationResult("unused", expected, a, "success", forbiddenFallback),
      /different PR head, result ID or bound/,
    );
  });
for (const status of ["checking-failed", "invalid-submission", "checking"])
  test(`${status} cannot use a local fallback`, () => {
    const a = {
      ...expected,
      status,
      reason: "The submitted theorem was rejected",
    };
    let called = false;
    assert.throws(
      () =>
        verificationResult("unused", expected, a, "failure", () => {
          called = true;
          return {};
        }),
      { message: a.reason },
    );
    assert.equal(called, false);
  });
for (const status of ["infrastructure-blocked", "resource-exhausted"])
  test(`${status} can use a matching independently checked local run`, () => {
    const report = accepted().report;
    let calls = 0;
    assert.equal(
      verificationResult(
        "base",
        expected,
        { ...expected, status, reason: "Worker memory limit" },
        "failure",
        (root, e) => {
          assert.equal(root, "base");
          assert.deepEqual(e, expected);
          calls++;
          return report;
        },
      ),
      report,
    );
    assert.equal(calls, 1);
    assert.throws(
      () =>
        verificationResult(
          "base",
          expected,
          { ...expected, status, reason: "Worker memory limit" },
          "failure",
          () => {
            throw Error("No matching receipt");
          },
        ),
      /Worker memory limit.*suitable worker/,
    );
  });
test("requires a successful worker job as well as its acceptance report", () => {
  assert.throws(
    () =>
      verificationResult(
        "base",
        expected,
        accepted(),
        "failure",
        forbiddenFallback,
      ),
    /job did not complete/,
  );
});
for (const [key, value] of [
  ["kernels", ["Lean default"]],
  ["allowed_axioms", ["propext", "Classical.choice", "Quot.sound", "sorryAx"]],
  ["targets", ["Candidate.bound"]],
  ["candidate_mount_preflight", "FAIL"],
  ["reviewed_pr_head", "b".repeat(40)],
])
  test(`rejects incomplete acceptance: ${key}`, () => {
    const a = accepted();
    a.report[key] = value;
    assert.throws(
      () =>
        verificationResult("base", expected, a, "success", forbiddenFallback),
      /canonical bound with all three kernels/,
    );
  });
