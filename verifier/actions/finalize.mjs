// Runs in the publishing job, using only base-branch code and same-run artifacts.
import { readFileSync, existsSync, writeFileSync } from "node:fs";
import { api } from "../github-api.mjs";
import { parseDeclaration } from "../pr-admission.mjs";
import { validateDecimalApproximation } from "../pr-decimal.mjs";
import { verificationResult } from "./result.mjs";
import { workerCertificate } from "../certificate.mjs";
const c = JSON.parse(readFileSync("verification-context/context.json", "utf8"));
if (
  c.repository !== process.env.GITHUB_REPOSITORY ||
  c.run_id !== process.env.GITHUB_RUN_ID ||
  c.run_attempt !== process.env.GITHUB_RUN_ATTEMPT ||
  c.workflow_sha !== process.env.GITHUB_WORKFLOW_SHA ||
  process.env.GITHUB_REF !== `refs/heads/${c.defaultBranch}`
)
  throw Error(
    "Verification context does not belong to this protected workflow run",
  );
let conclusion = "failure",
  summary;
try {
  const p = await api(`repos/${c.repository}/pulls/${c.expected.number}`);
  const identity = (p) =>
    JSON.stringify([
      p.state,
      p.head.sha,
      p.base.sha,
      p.base.ref,
      p.base.repo.full_name,
      p.body,
      p.changed_files,
    ]);
  if (identity(p) !== identity(c.pr))
    throw Error(
      "PR head, base or declaration changed during verification; rerun admission",
    );
  const attempt = existsSync("verification/attempt.json")
    ? JSON.parse(readFileSync("verification/attempt.json", "utf8"))
    : null;
  const report = verificationResult(
    process.cwd(),
    c.expected,
    attempt,
    process.env.QRH_VERIFICATION_RESULT,
  );
  const declaration = parseDeclaration(p.body);
  validateDecimalApproximation({
    ...declaration,
    bound_interval: report.bound_interval,
    catalogue: JSON.parse(readFileSync("catalogue/results.json", "utf8")),
  });
  const record =
    attempt.status === "accepted"
      ? workerCertificate(
          c.expected,
          report,
          `https://github.com/${c.repository}/actions/runs/${c.run_id}/attempts/${c.run_attempt}`,
          readFileSync("verification/run/result.json"),
        )
      : report;
  writeFileSync(
    "verification/certificate.json",
    JSON.stringify(record, null, 2) + "\n",
  );
  conclusion = "success";
  summary = `Proof verification accepts ${c.expected.result_id} at ${c.expected.theta_exact} for this exact PR head. Decimal ${declaration.theta_decimal} accurately approximates the exact bound.`;
  if (attempt.status !== "accepted")
    summary +=
      " A matching independently verified local run supplied the result because hosted verification was unavailable.";
} catch (error) {
  summary = `Admission failed: ${error.message}`;
  process.exitCode = 1;
}
const response = await fetch(
  `https://api.github.com/repos/${c.repository}/check-runs/${c.check_id}`,
  {
    method: "PATCH",
    headers: {
      Authorization: `Bearer ${process.env.GITHUB_TOKEN}`,
      "Content-Type": "application/json",
      Accept: "application/vnd.github+json",
    },
    body: JSON.stringify({
      status: "completed",
      conclusion,
      completed_at: new Date().toISOString(),
      output: {
        title:
          conclusion === "success"
            ? "PR admission requirements satisfied"
            : "PR admission failed",
        summary,
      },
    }),
  },
);
if (!response.ok)
  throw Error(`Publishing admission failed: HTTP ${response.status}`);
console.log(summary);
