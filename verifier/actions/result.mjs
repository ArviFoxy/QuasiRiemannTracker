// These reports are produced by this workflow run, outside candidate mounts.
import { readFileSync, existsSync } from "node:fs";
import { join } from "node:path";
import { validateAdmission } from "../pr-evidence.mjs";
export const identityKeys = [
  "repository",
  "number",
  "head_sha",
  "result_id",
  "theta_exact",
];
export function verificationResult(
  root,
  expected,
  attempt,
  jobResult = "success",
  fallback = validateAdmission,
) {
  if (!attempt || !identityKeys.every((k) => attempt[k] === expected[k]))
    throw Error(
      "Verification report is missing or belongs to a different PR head, result ID or bound",
    );
  if (
    ["infrastructure-blocked", "resource-exhausted"].includes(attempt.status)
  ) {
    try {
      return fallback(root, expected);
    } catch {
      throw Error(
        `${attempt.reason}. Retry verification on a suitable worker, or register a matching independently verified local run.`,
      );
    }
  }
  if (attempt.status !== "accepted")
    throw Error(attempt.reason || "Proof verification did not complete");
  if (jobResult !== "success")
    throw Error("Verification job did not complete successfully");
  const r = attempt.report;
  if (
    r?.status !== "PASS" ||
    r.reviewed_pr_head !== expected.head_sha ||
    r.source_repository !== expected.repository ||
    r.result_id !== expected.result_id ||
    r.theta_exact !== expected.theta_exact ||
    r.judge_exit_code !== 0 ||
    JSON.stringify(r.targets) !== JSON.stringify(["QRH.canonical_bound"]) ||
    JSON.stringify(r.kernels) !==
      JSON.stringify(["Lean default", "nanoda", "con-ron"]) ||
    JSON.stringify([...(r.allowed_axioms ?? [])].sort()) !==
      JSON.stringify(["Classical.choice", "Quot.sound", "propext"]) ||
    r.sandbox_preflight !== "PASS" ||
    r.candidate_mount_preflight !== "PASS" ||
    r.challenge_exported_before_candidate_execution !== true ||
    r.receipt_outside_candidate !== true
  )
    throw Error(
      "Verification report does not establish the canonical bound with all three kernels",
    );
  return r;
}
export function currentVerification(root, expected) {
  const filename = join(root, "verification/attempt.json");
  if (!existsSync(filename))
    throw Error("Proof verification has not run for this PR head");
  return verificationResult(
    root,
    expected,
    JSON.parse(readFileSync(filename, "utf8")),
    process.env.QRH_VERIFICATION_RESULT,
  );
}
