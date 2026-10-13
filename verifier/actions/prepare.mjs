// Fetch immutable Git objects; never check out or execute the submitted project.
import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { submission } from "../manifest.mjs";
import { upstreamImports } from "./imports.mjs";
const c = JSON.parse(readFileSync("verification-context/context.json", "utf8"));
const e = c.expected;
mkdirSync("verification", { recursive: true });
const result = (status, reason) =>
  writeFileSync(
    "verification/attempt.json",
    JSON.stringify({ ...e, status, reason }, null, 2) + "\n",
  );
result("infrastructure-blocked", "Worker setup did not complete");
if (
  !/^[A-Za-z0-9_.-]+\/[A-Za-z0-9_.-]+$/.test(e.repository) ||
  !/^[a-f0-9]{40}$/.test(e.head_sha) ||
  !/^[a-z][a-z0-9-]{2,63}$/.test(e.result_id)
)
  throw Error("Invalid verification identity");
if (!/^[0-9]+\/[0-9]+$/.test(e.theta_exact)) {
  const reason =
    "The standard hosted worker supports rational bounds; this exact expression requires an algebraic checking profile";
  result("infrastructure-blocked", reason);
  console.error(reason);
  process.exit(1);
}
class WorkerProfileUnavailable extends Error {}
const env = {
  PATH: process.env.PATH,
  HOME: process.env.RUNNER_TEMP || process.env.HOME,
  GIT_CONFIG_NOSYSTEM: "1",
  GIT_CONFIG_GLOBAL: "/dev/null",
  GIT_TERMINAL_PROMPT: "0",
};
const git = (args) =>
  execFileSync("git", ["-c", "core.hooksPath=/dev/null", ...args], {
    env,
    stdio: "pipe",
    timeout: 300_000,
    maxBuffer: 12 * 1024 ** 2,
  });
git(["init", "--bare", "verification/source.git"]);
git([
  "-C",
  "verification/source.git",
  "fetch",
  "--depth=1",
  "--no-tags",
  `https://github.com/${e.repository}.git`,
  e.head_sha,
]);
try {
  const listing = git([
    "-C",
    "verification/source.git",
    "ls-tree",
    e.head_sha,
    "--",
    `submissions/${e.result_id}/manifest.json`,
  ]).toString();
  if (!listing)
    throw new WorkerProfileUnavailable(
      `Add submissions/${e.result_id}/manifest.json and its Lean proof in the standard submission layout`,
    );
  // Preparation binds source and generates the theorem before provisioning libraries.
  writeFileSync("verification/empty-libraries.json", "{}\n");
  execFileSync(
    process.execPath,
    [
      "verifier/standard/prepare.mjs",
      "--checkout",
      "verification/source.git",
      "--head",
      e.head_sha,
      "--repository",
      e.repository,
      "--id",
      e.result_id,
      "--libraries",
      "verification/empty-libraries.json",
      "--out",
      "verification/prepared",
    ],
    { env, stdio: "pipe" },
  );
  const s = submission("verification/prepared/submission");
  if (
    `${s.manifest.theta.numerator}/${s.manifest.theta.denominator}` !==
    e.theta_exact
  )
    throw Error("Submission manifest bound must equal QRH-Bound");
  const contract = JSON.parse(
    readFileSync("verification/prepared/contract.json", "utf8"),
  );
  // Only the pinned upstream OAI modules named in the source are built; source is data here.
  const imports = new Set();
  for (const f of s.files.filter((f) => f.path.endsWith(".lean"))) {
    for (const name of upstreamImports(f.bytes.toString())) imports.add(name);
  }
  writeFileSync(
    "verification/imports.json",
    JSON.stringify([...imports].sort()) + "\n",
  );
  console.log(`Prepared ${contract.manifest.id} at ${e.head_sha}`);
} catch (error) {
  const detail = error.stderr?.toString() || error.message;
  result(
    error instanceof WorkerProfileUnavailable
      ? "infrastructure-blocked"
      : "invalid-submission",
    detail.slice(-4000),
  );
  console.error(detail);
  process.exitCode = 1;
}
