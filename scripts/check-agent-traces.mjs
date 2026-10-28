// Local pre-push check: scan the same embedded metadata field as CI.
import { existsSync, lstatSync, readdirSync, readFileSync } from "node:fs";
import { relative, resolve, sep, join } from "node:path";
import { metadataDirectory, scanTrace } from "../verifier/agent-traces.mjs";
import { maxMetadataBytes } from "../verifier/submission-metadata.mjs";

try {
  const root = process.cwd();
  const submissions = join(root, "submissions");
  const directory = (path) => {
    const stat = lstatSync(path);
    if (!stat.isDirectory() || stat.isSymbolicLink())
      throw Error("Expected a regular submission directory");
  };
  let paths = process.argv.slice(2);
  if (!paths.length && existsSync(submissions)) {
    directory(submissions);
    paths = readdirSync(submissions).map((name) =>
      join(submissions, name, "metadata.json"),
    );
  }
  let count = 0;
  for (const input of paths) {
    const full = resolve(input);
    const path = relative(root, full).split(sep).join("/");
    const folder = metadataDirectory(path);
    if (!folder)
      throw Error("Select submissions/<submission-folder>/metadata.json");
    directory(submissions);
    directory(join(submissions, folder));
    const stat = lstatSync(full);
    if (!stat.isFile() || stat.isSymbolicLink())
      throw Error("Expected a regular submission metadata.json");
    if (stat.size > maxMetadataBytes)
      throw Error("Submission metadata must be at most 2 MiB");
    count += scanTrace(path, readFileSync(full));
  }
  console.log(
    `Agent traces: ${count} embedded exports checked; no suspected secrets found.`,
  );
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}
