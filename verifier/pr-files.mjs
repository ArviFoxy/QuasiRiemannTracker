import { execFileSync } from "node:child_process";
import { mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { pages } from "./github-api.mjs";

const sha = (value) => /^[a-f0-9]{40}$/.test(value ?? "");
function git(directory, args) {
  return execFileSync("git", ["-c", "core.hooksPath=/dev/null", ...args], {
    cwd: directory,
    encoding: "utf8",
    timeout: 180_000,
    maxBuffer: 32 * 1024 * 1024,
    env: {
      PATH: process.env.PATH,
      GIT_CONFIG_NOSYSTEM: "1",
      GIT_CONFIG_GLOBAL: "/dev/null",
      GIT_TERMINAL_PROMPT: "0",
      GIT_NO_REPLACE_OBJECTS: "1",
      GIT_ALLOW_PROTOCOL: "https",
    },
    stdio: ["ignore", "pipe", "pipe"],
  });
}

export function gitChangedFiles(directory, base, head) {
  if (!sha(base) || !sha(head)) throw Error("Invalid diff commit");
  const ancestor = git(directory, ["merge-base", base, head]).trim();
  if (!sha(ancestor)) throw Error("Invalid merge base");
  const fields = git(directory, [
    "diff",
    "--no-ext-diff",
    "--no-textconv",
    "--find-renames",
    "--name-status",
    "-z",
    ancestor,
    head,
    "--",
  ]).split("\0");
  if (fields.pop() !== "") throw Error("Incomplete Git diff");
  const files = [];
  for (let i = 0; i < fields.length; ) {
    const kind = fields[i++];
    if (!/^(?:[AMDT]|R\d+)$/.test(kind))
      throw Error("Unexpected Git diff status");
    const first = fields[i++];
    const filename = kind.startsWith("R") ? fields[i++] : first;
    if (!first || !filename) throw Error("Incomplete Git diff path");
    files.push({
      filename,
      status: kind.startsWith("R")
        ? "renamed"
        : { A: "added", D: "removed", M: "modified", T: "modified" }[kind],
      ...(kind.startsWith("R") ? { previous_filename: first } : {}),
    });
  }
  return files;
}

function fetchChangedFiles(pr, repository) {
  if (
    !/^[\w.-]+\/[\w.-]+$/.test(repository) ||
    pr.base?.repo?.full_name !== repository ||
    !sha(pr.base?.sha) ||
    !sha(pr.head?.sha)
  )
    throw Error("Invalid PR diff identity");
  const directory = mkdtempSync(join(tmpdir(), "qrh-pr-diff-"));
  try {
    git(directory, ["init", "--bare", "--template="]);
    git(directory, [
      "remote",
      "add",
      "origin",
      `https://github.com/${repository}.git`,
    ]);
    git(directory, ["config", "remote.origin.promisor", "true"]);
    git(directory, ["config", "remote.origin.partialclonefilter", "blob:none"]);
    git(directory, [
      "fetch",
      "--no-tags",
      "--filter=blob:none",
      "origin",
      pr.base.sha,
      pr.head.sha,
    ]);
    return gitChangedFiles(directory, pr.base.sha, pr.head.sha);
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

export async function prFiles(
  pr,
  repository,
  {
    apiFiles = () => pages(`repos/${repository}/pulls/${pr.number}/files`),
    gitFiles = () => fetchChangedFiles(pr, repository),
  } = {},
) {
  // GitHub returns at most 3,000 changed files. Read larger diffs from immutable
  // commits in a temporary bare repository; candidate files are never checked out.
  if (pr.changed_files > 3000) {
    const files = await gitFiles();
    if (
      files.length !== pr.changed_files ||
      new Set(files.map((f) => f.filename)).size !== files.length
    )
      throw Error("Git diff disagrees with PR changed-file count");
    return files;
  }
  return apiFiles();
}
