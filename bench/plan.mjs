// List the Lean modules each submission compiles, using the verifier's own
// import-closure logic so the benchmark measures what admission builds.
//   node bench/plan.mjs --package-imports      pinned-package modules to prebuild
//   node bench/plan.mjs --out DIR [ID...]      write DIR/<id>.json (default: all)
import { execFileSync } from "node:child_process";
import { mkdirSync, readdirSync, writeFileSync } from "node:fs";
import { dirname, join, resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { parseArgs } from "node:util";
import { submission } from "../verifier/manifest.mjs";
import { dependencyGraph } from "../verifier/submission-dependencies.mjs";
import { leanImports } from "../verifier/actions/imports.mjs";

const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
const git = (...args) =>
  execFileSync("git", ["-C", root, ...args], { encoding: "utf8" }).trim();
const packageImport = /^(PrimeNumberTheoremAnd|RellichKondrachov)(\.|$)/;

// The import graph does not depend on the bound; any valid one will do.
// Most submissions share the baseline, so read each directory only once.
const loaded = new Map();
const load = (id) => {
  if (!loaded.has(id))
    loaded.set(
      id,
      submission(join(root, "submissions", id), {
        id,
        theta: { numerator: "1", denominator: "1" },
      }),
    );
  return loaded.get(id);
};

export function plan(id) {
  const graph = dependencyGraph(id, load);
  const lines = (bytes) => bytes.toString().split("\n").length - 1;
  const modules = graph.order.map((name) => {
    const { owner, file } = graph.modules.get(name);
    return {
      name,
      owner,
      path: file.path,
      sha256: file.sha256,
      bytes: file.bytes.length,
      lines: lines(file.bytes),
      dependencies: graph.dependencies[name],
      package_imports: leanImports(file.bytes.toString()).filter((name) =>
        packageImport.test(name),
      ),
    };
  });
  return {
    id,
    // The same tree identities the admission archive binds to a verified result.
    source_tree: git("rev-parse", `HEAD:submissions/${id}/src`),
    dependency_trees: Object.fromEntries(
      [...graph.submissions.keys()].map((dependency) => [
        dependency,
        git("rev-parse", `HEAD:submissions/${dependency}`),
      ]),
    ),
    modules,
  };
}

const { values, positionals } = parseArgs({
  options: {
    "package-imports": { type: "boolean" },
    out: { type: "string" },
  },
  allowPositionals: true,
});
const ids = positionals.length
  ? positionals
  : readdirSync(join(root, "submissions")).sort();
if (git("status", "--porcelain", "--", "submissions"))
  throw Error("Plan from committed sources: submissions/ has local changes");
if (values["package-imports"]) {
  const modules = new Set(
    ids.flatMap((id) =>
      plan(id).modules.flatMap((module) => module.package_imports),
    ),
  );
  console.log(JSON.stringify([...modules].sort()));
} else if (values.out) {
  mkdirSync(values.out, { recursive: true });
  for (const id of ids) {
    const p = plan(id);
    writeFileSync(join(values.out, `${id}.json`), JSON.stringify(p) + "\n");
    console.log(`${id}: ${p.modules.length} modules`);
  }
} else throw Error("Usage: plan.mjs (--package-imports | --out DIR) [ID...]");
