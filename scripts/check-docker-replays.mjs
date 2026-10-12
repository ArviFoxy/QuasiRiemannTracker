import { readFileSync } from "node:fs";
import { validateAdmission } from "../verifier/pr-evidence.mjs";

const policy = JSON.parse(readFileSync("verifier/pr-admissions.json", "utf8"));
let checked = 0;
for (const entry of policy.admissions) {
  if (!(entry.pin.replay_profile ?? "").startsWith("docker-")) continue;
  const { repository, number, head_sha, result_id, theta_exact } = entry;
  validateAdmission(process.cwd(), {
    repository,
    number,
    head_sha,
    result_id,
    theta_exact,
  });
  checked++;
}
console.log(
  `Authenticated ${checked} independently executed Docker replay dossiers.`,
);
