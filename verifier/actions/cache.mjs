import { createHash } from "node:crypto";
import {
  appendFileSync,
  mkdirSync,
  readFileSync,
  readdirSync,
  writeFileSync,
} from "node:fs";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { upstreamImports } from "./imports.mjs";

const inputs = [
  "verifier/pins.json",
  "verifier/worker_resources.py",
  "verifier/standard/tool-pins.json",
  "verifier/standard/lakefile.lean",
  "verifier/standard/lake-manifest.json",
  "verifier/actions/setup.py",
  "verifier/actions/library_contract.py",
  "verifier/actions/imports.mjs",
  "verifier/actions/cache.mjs",
  ".github/actions/verifier-cache/action.yml",
];

export function cachePlan(root, { os, arch }) {
  if (os !== "Linux" || arch !== "X64")
    throw new Error("The pinned checking environment requires Linux X64");
  // Every consumer reads the same checkout's submissions, independently of its
  // selected PR/result. Only module names from the pinned upstream are built.
  const imports = [
    ...new Set(
      readdirSync(resolve(root, "submissions"), { recursive: true })
        .filter((name) => name.endsWith(".lean"))
        .flatMap((name) =>
          upstreamImports(
            readFileSync(resolve(root, "submissions", name), "utf8"),
          ),
        ),
    ),
  ].sort();
  const hash = createHash("sha256");
  for (const name of inputs) {
    hash.update(name + "\0");
    hash.update(readFileSync(resolve(root, name)));
    hash.update("\0");
  }
  const prefix = `qrh-environment-v1-ubuntu24.04-${os}-${arch}-${hash.digest("hex")}-`;
  return {
    prefix,
    key:
      prefix +
      createHash("sha256").update(JSON.stringify(imports)).digest("hex"),
    path: "verification/environment",
    imports,
  };
}

if (
  process.argv[1] &&
  resolve(process.argv[1]) === fileURLToPath(import.meta.url)
) {
  const plan = cachePlan(process.cwd(), {
    os: process.env.RUNNER_OS,
    arch: process.env.RUNNER_ARCH,
  });
  mkdirSync("verification", { recursive: true });
  writeFileSync(
    "verification/cache-imports.json",
    JSON.stringify(plan.imports) + "\n",
  );
  appendFileSync(
    process.env.GITHUB_OUTPUT,
    `key=${plan.key}\nprefix=${plan.prefix}\npath=${plan.path}\n`,
  );
  console.log(
    `Shared environment: ${plan.key}; ${plan.imports.length} upstream targets`,
  );
}
