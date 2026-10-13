import { sha256 } from "./common.mjs";
export const KERNELS = ["Lean default", "nanoda", "con-ron"];
export function certificate(value) {
  if (
    value?.schema_version !== 1 ||
    !/^[a-z][a-z0-9-]{2,63}$/.test(value.result_id ?? "") ||
    typeof value.theta_exact !== "string" ||
    !value.theta_exact.trim() ||
    value.theta_exact.length > 256 ||
    !Number.isFinite(Date.parse(value.verified_at)) ||
    !/^[\w.-]+\/[\w.-]+$/.test(value.source_repository ?? "") ||
    !/^[a-f0-9]{40}$/.test(value.source_commit ?? "") ||
    !/^[a-f0-9]{64}$/.test(value.report_sha256 ?? "") ||
    !/^https:\/\/github\.com\/[\w.-]+\/[\w.-]+\/(?:blob\/[a-f0-9]{40}\/[^\s]+|actions\/runs\/[0-9]+(?:\/attempts\/[0-9]+)?)$/.test(
      value.report_url ?? "",
    ) ||
    JSON.stringify(value.kernels) !== JSON.stringify(KERNELS)
  )
    throw Error("Invalid verification record");
  return value;
}
// Call after verificationResult has authenticated a successful worker report.
export function workerCertificate(expected, report, reportUrl) {
  return certificate({
    schema_version: 1,
    result_id: expected.result_id,
    theta_exact: expected.theta_exact,
    verified_at: report.verified_at,
    source_repository: expected.repository,
    source_commit: expected.head_sha,
    kernels: KERNELS,
    report_url: reportUrl,
    report_sha256: sha256(report),
    ...(report.bound_interval ? { bound_interval: report.bound_interval } : {}),
  });
}
