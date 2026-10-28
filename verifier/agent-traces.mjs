// Optional research logs are untrusted data, separate from certified proof trees.
import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { TextDecoder } from "node:util";
import { validateSubmissionDirectory } from "./submission-paths.mjs";

export const traceLimits = {
  fileBytes: 10 * 1024 ** 2,
  totalBytes: 50 * 1024 ** 2,
  files: 50,
};
const sha = (value) => /^[a-f0-9]{40}$/.test(value ?? "");

export function traceDirectory(path) {
  const match =
    /^agent-traces\/([^/]+)\/[A-Za-z0-9][A-Za-z0-9_-]{0,99}\.(?:json|jsonl)$/.exec(
      path ?? "",
    );
  if (!match) return null;
  try {
    return validateSubmissionDirectory(match[1]);
  } catch {
    return null;
  }
}

export function traceContents(path, bytes) {
  if (!traceDirectory(path)) throw Error("Invalid agent trace path");
  if (!bytes.length || bytes.length > traceLimits.fileBytes)
    throw Error(`Agent trace must be nonempty and at most 10 MiB: ${path}`);
  let raw, values;
  try {
    raw = new TextDecoder("utf-8", { fatal: true }).decode(bytes);
    values = path.endsWith(".jsonl")
      ? raw
          .split(/\r?\n/)
          .filter((line) => line.trim())
          .map((line) => {
            const value = JSON.parse(line);
            if (!value || typeof value !== "object" || Array.isArray(value))
              throw Error();
            return value;
          })
      : [JSON.parse(raw)];
    if (!values.length || values.some((v) => !v || typeof v !== "object"))
      throw Error();
  } catch {
    // JSON.parse errors can contain fragments of a credential-bearing trace.
    throw Error(`Invalid UTF-8 JSON object/array or JSONL objects: ${path}`);
  }
  // Scan strings after JSON unescaping as well as the original export. Preserve
  // key/value context for generic-key rules and actual newlines in tool output.
  const decoded = [],
    pending = values.map((value) => ["", value]);
  while (pending.length) {
    const [key, value] = pending.pop();
    if (typeof value === "string") decoded.push(`${key}: ${value}`);
    else if (value && typeof value === "object") {
      for (const [name, child] of Object.entries(value)) {
        decoded.push(name);
        pending.push([name, child]);
      }
    }
  }
  return { raw, decoded: decoded.join("\n") };
}

export function scanTrace(path, bytes) {
  const { raw, decoded } = traceContents(path, bytes);
  const directory = mkdtempSync(join(tmpdir(), "qrh-trace-"));
  try {
    // Use built-in rules from the pinned scanner, never submitted configuration,
    // baselines, ignore files, or inline allow comments. No keys are verified.
    writeFileSync(
      join(directory, "rules.toml"),
      "[extend]\nuseDefault = true\n",
      { mode: 0o600 },
    );
    writeFileSync(join(directory, "ignore"), "", { mode: 0o600 });
    writeFileSync(join(directory, "raw.json"), raw, { mode: 0o600 });
    writeFileSync(join(directory, "decoded.txt"), decoded, { mode: 0o600 });
    const result = spawnSync(
      process.env.QRH_GITLEAKS || "gitleaks",
      [
        "dir",
        "--config",
        join(directory, "rules.toml"),
        "--gitleaks-ignore-path",
        join(directory, "ignore"),
        "--ignore-gitleaks-allow",
        "--redact=100",
        "--no-banner",
        "--no-color",
        "--log-level",
        "error",
        "--max-decode-depth",
        "2",
        "--timeout",
        "60",
        directory,
      ],
      {
        cwd: directory,
        env: { PATH: process.env.PATH, HOME: directory },
        encoding: "utf8",
        // Allow the trusted CI wrapper to download the pinned binary on first use.
        timeout: 180_000,
        maxBuffer: 1024 ** 2,
        stdio: ["ignore", "pipe", "pipe"],
      },
    );
    // Never forward scanner output, even on failure: it may contain secrets.
    if (!result.error && result.status === 1)
      throw Error(
        `Possible secret in agent trace ${path}; redact it and revoke any exposed credential`,
      );
    if (result.error || result.status !== 0)
      throw Error(
        "Agent trace secret scan could not complete; install Gitleaks 8.30.1 and retry",
      );
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

export function validateTraceSizes(files) {
  if (
    files.length > traceLimits.files ||
    files.some(
      (f) =>
        !Number.isSafeInteger(f.size) ||
        f.size < 1 ||
        f.size > traceLimits.fileBytes,
    ) ||
    files.reduce((n, f) => n + f.size, 0) > traceLimits.totalBytes
  )
    throw Error(
      "Agent trace size limit: 10 MiB per file, 50 MiB and 50 files per submission",
    );
}

// Read only immutable Git trees/blobs. Candidate code and local configuration
// are never checked out or executed by the trusted admission controller.
export async function validatePRTraces({
  request,
  repository,
  pr,
  files,
  scan = scanTrace,
}) {
  const changed = files
    .flatMap((file) => [file.filename, file.previous_filename].filter(Boolean))
    .filter(
      (path) => path === "agent-traces" || path.startsWith("agent-traces/"),
    )
    .filter((path) => path !== "agent-traces/README.md");
  if (!changed.length) return 0;
  if (!/^[\w.-]+\/[\w.-]+$/.test(repository ?? "") || !sha(pr.head?.sha))
    throw Error("Invalid agent trace PR identity");
  const folders = new Set();
  for (const path of changed) {
    const folder = traceDirectory(path);
    if (!folder)
      throw Error(
        "Agent traces must use agent-traces/<submission-folder>/<run-name>.json or .jsonl",
      );
    folders.add(folder);
  }
  const tree = async (id) => {
    const response = await request(`repos/${repository}/git/trees/${id}`);
    if (
      response.truncated ||
      !Array.isArray(response.tree) ||
      new Set(response.tree.map((e) => e.path)).size !== response.tree.length
    )
      throw Error("Incomplete or ambiguous agent trace tree");
    return response.tree;
  };
  const child = (entries, name) => {
    const entry = entries.find((e) => e.path === name);
    if (
      entry &&
      (entry.type !== "tree" || entry.mode !== "040000" || !sha(entry.sha))
    )
      throw Error("Expected a regular agent trace/submission directory");
    return entry;
  };
  const root = await tree(pr.head.sha);
  const traces = child(root, "agent-traces");
  if (!traces) {
    if (files.some((f) => f.status !== "removed" && traceDirectory(f.filename)))
      throw Error("Changed agent trace is missing from the PR head");
    return 0;
  }
  const entries = await tree(traces.sha);
  const submissions = child(root, "submissions");
  const submitted = submissions ? await tree(submissions.sha) : [];
  let count = 0;
  for (const folder of folders) {
    const entry = child(entries, folder);
    if (!entry) {
      if (
        files.some(
          (f) =>
            f.status !== "removed" && traceDirectory(f.filename) === folder,
        )
      )
        throw Error("Changed agent trace is missing from the PR head");
      continue;
    }
    if (!child(submitted, folder))
      throw Error(
        `Agent traces must match an existing submission directory: ${folder}`,
      );
    const contents = await tree(entry.sha);
    const names = new Set(
      contents.map((file) => `agent-traces/${folder}/${file.path}`),
    );
    if (
      files.some(
        (file) =>
          file.status !== "removed" &&
          traceDirectory(file.filename) === folder &&
          !names.has(file.filename),
      )
    )
      throw Error("Changed agent trace is missing from the PR head");
    for (const file of contents)
      if (
        !traceDirectory(`agent-traces/${folder}/${file.path}`) ||
        file.type !== "blob" ||
        file.mode !== "100644" ||
        !sha(file.sha)
      )
        throw Error(
          "Agent traces must be regular JSON/JSONL files; directories, symlinks and executable files are not allowed",
        );
    validateTraceSizes(contents);
    for (const file of contents) {
      const blob = await request(`repos/${repository}/git/blobs/${file.sha}`);
      if (
        blob.encoding !== "base64" ||
        typeof blob.content !== "string" ||
        blob.size !== file.size ||
        blob.content.length >
          Math.ceil(traceLimits.fileBytes / 3) * 4 + 1024 * 1024
      )
        throw Error("Invalid agent trace blob");
      const bytes = Buffer.from(blob.content, "base64");
      if (bytes.length !== file.size)
        throw Error("Agent trace blob size mismatch");
      scan(`agent-traces/${folder}/${file.path}`, bytes);
      count++;
    }
  }
  return count;
}
