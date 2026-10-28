// Local pre-push check: use the same parser, limits and secret scanner as CI.
import { existsSync, lstatSync, readdirSync, readFileSync } from "node:fs";
import { relative, resolve, sep, join } from "node:path";
import {
  scanTrace,
  traceDirectory,
  validateTraceSizes,
} from "../verifier/agent-traces.mjs";

try {
  const root = process.cwd();
  const directory = join(root, "agent-traces");
  let folders = process.argv.slice(2);
  if (!folders.length && existsSync(directory)) {
    if (
      !lstatSync(directory).isDirectory() ||
      lstatSync(directory).isSymbolicLink()
    )
      throw Error("Expected a regular agent-traces directory");
    folders = readdirSync(directory)
      .filter((name) => name !== "README.md")
      .map((name) => join(directory, name));
  }
  let count = 0;
  for (const folder of folders) {
    const full = resolve(folder);
    const path = relative(root, full).split(sep).join("/");
    const name = traceDirectory(`${path}/trace.json`);
    if (
      !name ||
      !lstatSync(directory).isDirectory() ||
      lstatSync(directory).isSymbolicLink() ||
      !lstatSync(full).isDirectory() ||
      lstatSync(full).isSymbolicLink()
    )
      throw Error(
        "Select a regular agent-traces/<submission-folder> directory",
      );
    const submission = join(root, "submissions", name);
    if (
      !existsSync(submission) ||
      !lstatSync(submission).isDirectory() ||
      lstatSync(submission).isSymbolicLink()
    )
      throw Error(
        `Agent traces must match an existing submission directory: ${name}`,
      );
    const files = readdirSync(full).map((file) => {
      const filePath = `${path}/${file}`;
      const stat = lstatSync(join(full, file));
      if (
        !traceDirectory(filePath) ||
        !stat.isFile() ||
        stat.isSymbolicLink() ||
        stat.mode & 0o111
      )
        throw Error(
          "Agent traces must be regular, non-executable JSON/JSONL files",
        );
      return { path: filePath, full: join(full, file), size: stat.size };
    });
    validateTraceSizes(files);
    for (const file of files) {
      scanTrace(file.path, readFileSync(file.full));
      count++;
    }
  }
  console.log(
    `Agent traces: ${count} files checked; no suspected secrets found.`,
  );
} catch (error) {
  console.error(error.message);
  process.exitCode = 1;
}
