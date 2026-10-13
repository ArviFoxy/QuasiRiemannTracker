// Run from a trusted checkout. Read submission Git blobs as data.
import { execFileSync } from "node:child_process";
import { mkdirSync, readFileSync, writeFileSync } from "node:fs";
import { resolve, dirname, join } from "node:path";
import { parseArgs } from "node:util";
import { exactBound } from "../../core/exact-bound.mjs";
import { submission, safePath } from "../manifest.mjs";
import { challenge, solutionWrapper } from "../challenge.mjs";
import { sha256 } from "../common.mjs";
const { values: v } = parseArgs({
  options: Object.fromEntries(
    [
      "checkout",
      "head",
      "repository",
      "id",
      "libraries",
      "bound",
      "source-commit",
      "out",
    ].map((k) => [k, { type: "string" }]),
  ),
});
if (
  !/^[a-f0-9]{40}$/.test(v.head ?? "") ||
  !/^[\w.-]+\/[\w.-]+$/.test(v.repository ?? "") ||
  !/^[a-z][a-z0-9-]{2,63}$/.test(v.id ?? "")
)
  throw Error("Invalid source identity");
const out = resolve(v.out),
  prefix = `submissions/${v.id}/`;
mkdirSync(out);
const source = join(out, "submission");
mkdirSync(source);
const git = (args) =>
  execFileSync("git", ["-C", resolve(v.checkout), ...args], {
    maxBuffer: 12 * 1024 * 1024,
  });
const entries = git(["ls-tree", "-rz", v.head, "--", prefix])
  .toString()
  .split("\0")
  .filter(Boolean);
if (!entries.length || entries.length > 512)
  throw Error("Invalid submission file count");
for (const row of entries) {
  const match = /^(100644|100755) blob ([a-f0-9]{40})\t(.+)$/.exec(row);
  if (!match) throw Error("Submission requires regular Git files");
  const name = safePath(match[3].slice(prefix.length)),
    file = join(source, name);
  mkdirSync(dirname(file), { recursive: true });
  writeFileSync(file, git(["cat-file", "blob", match[2]]), { mode: 0o444 });
}
const s = submission(source, { id: v.id, ...exactBound(v.bound) });
const sourceCommit = v["source-commit"] ?? v.head;
if (!/^[a-f0-9]{40}$/.test(sourceCommit))
  throw Error("Invalid original source commit");
const originalTree = git([
  "ls-tree",
  "-rz",
  sourceCommit,
  "--",
  prefix,
]).toString();
if (originalTree !== entries.join("\0") + "\0")
  throw Error("Original source differs from the reviewed head");
if (s.manifest.id !== v.id) throw Error("Submission ID differs");
const modules = new Map(
  s.files
    .filter((f) => f.path.endsWith(".lean"))
    .map((f) => [f.path.slice(4, -5).replaceAll("/", "."), f.bytes.toString()]),
);
const done = new Set(),
  active = new Set(),
  order = [];
function visit(name) {
  if (done.has(name)) return;
  if (active.has(name)) throw Error("Cyclic candidate imports");
  active.add(name);
  for (const line of modules.get(name).split("\n")) {
    const m = /^\s*(?:public\s+)?import\s+(.+)$/.exec(line);
    if (m)
      for (const dep of m[1].split("--")[0].trim().split(/\s+/))
        if (dep.startsWith("Candidate.")) {
          if (!modules.has(dep)) throw Error("Missing candidate module");
          visit(dep);
        }
  }
  active.delete(name);
  done.add(name);
  order.push(name);
}
for (const name of modules.keys()) visit(name);
const generated = {
  "Challenge.lean": challenge(s.manifest),
  "Solution.lean": solutionWrapper(s.manifest),
};
for (const [name, body] of Object.entries(generated))
  writeFileSync(join(out, name), body, { mode: 0o444 });
const libraries = readFileSync(v.libraries);
writeFileSync(join(out, "libraries.json"), libraries, { mode: 0o444 });
writeFileSync(
  join(out, "contract.json"),
  JSON.stringify(
    {
      schema_version: 1,
      repository: v.repository,
      head_sha: v.head,
      source_commit: sourceCommit,
      manifest: s.manifest,
      source_files: Object.fromEntries(
        s.inventory.map((f) => [f.path, f.sha256]),
      ),
      build_order: order,
      generated_files: Object.fromEntries(
        Object.entries(generated).map(([k, b]) => [k, sha256(b)]),
      ),
      library_inventory_sha256: sha256(libraries),
    },
    null,
    2,
  ) + "\n",
  { mode: 0o444 },
);
console.log(
  `Prepared ${s.manifest.id} at ${v.head}: ${order.length} Lean modules`,
);
