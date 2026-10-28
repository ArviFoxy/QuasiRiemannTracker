// Embedded agent exports are untrusted data; scan without executing candidate code.
import { spawnSync } from "node:child_process";
import { mkdtempSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { submissionId } from "./submission-paths.mjs";
import {
  maxMetadataBytes,
  parseSubmissionMetadataJSON,
} from "./submission-metadata.mjs";

const sha = (value) => /^[a-f0-9]{40}$/.test(value ?? "");

export function metadataDirectory(path) {
  const match = /^submissions\/([^/]+)\/metadata\.json$/.exec(path ?? "");
  if (!match) return null;
  try {
    submissionId(match[1]);
    return match[1];
  } catch {
    return null;
  }
}

export function traceContents(path, bytes) {
  if (!metadataDirectory(path))
    throw Error("Select submissions/<submission-folder>/metadata.json");
  if (!bytes.length || bytes.length > maxMetadataBytes)
    throw Error("Submission metadata must be nonempty and at most 2 MiB");
  const metadata = parseSubmissionMetadataJSON(bytes);
  const traces = metadata.agent_traces ?? [];
  // Scan the original metadata and unescaped trace strings, retaining key/value
  // context and actual newlines in tool output for the scanner's built-in rules.
  const decoded = [],
    pending = traces.map((value) => ["", value]);
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
  return {
    raw: bytes.toString("utf8"),
    decoded: decoded.join("\n"),
    count: traces.length,
  };
}

export function scanTrace(path, bytes) {
  const { raw, decoded, count } = traceContents(path, bytes);
  if (!count) return 0;
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
        env: { PATH: process.env.PATH },
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
    return count;
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}

// Read only immutable Git trees/blobs; candidate configuration is never loaded.
export async function validatePRTraces({
  request,
  repository,
  pr,
  files,
  scan = scanTrace,
}) {
  const changed = [
    ...new Set(
      files
        .filter(
          (file) =>
            file.status !== "removed" && metadataDirectory(file.filename),
        )
        .map((file) => file.filename),
    ),
  ];
  if (!changed.length) return 0;
  if (!/^[\w.-]+\/[\w.-]+$/.test(repository ?? "") || !sha(pr.head?.sha))
    throw Error("Invalid agent trace PR identity");
  const tree = async (id) => {
    const response = await request(`repos/${repository}/git/trees/${id}`);
    if (
      response.truncated ||
      !Array.isArray(response.tree) ||
      new Set(response.tree.map((e) => e.path)).size !== response.tree.length
    )
      throw Error("Incomplete or ambiguous submission metadata tree");
    return response.tree;
  };
  const child = (entries, name) => {
    const entry = entries.find((e) => e.path === name);
    if (
      !entry ||
      entry.type !== "tree" ||
      entry.mode !== "040000" ||
      !sha(entry.sha)
    )
      throw Error("Expected a regular submission directory at the PR head");
    return entry;
  };
  const root = await tree(pr.head.sha);
  const submissions = await tree(child(root, "submissions").sha);
  let count = 0;
  for (const path of changed) {
    const entries = await tree(child(submissions, metadataDirectory(path)).sha);
    const file = entries.find((e) => e.path === "metadata.json");
    if (
      !file ||
      file.type !== "blob" ||
      !["100644", "100755"].includes(file.mode) ||
      !sha(file.sha)
    )
      throw Error("Expected a regular submission metadata.json");
    if (
      !Number.isSafeInteger(file.size) ||
      file.size < 1 ||
      file.size > maxMetadataBytes
    )
      throw Error("Submission metadata must be nonempty and at most 2 MiB");
    const blob = await request(`repos/${repository}/git/blobs/${file.sha}`);
    if (
      blob.encoding !== "base64" ||
      typeof blob.content !== "string" ||
      blob.size !== file.size ||
      blob.content.length >
        Math.ceil(maxMetadataBytes / 3) * 4 + maxMetadataBytes / 16
    )
      throw Error("Invalid submission metadata blob");
    const bytes = Buffer.from(blob.content, "base64");
    if (bytes.length !== file.size)
      throw Error("Submission metadata blob size mismatch");
    count += scan(path, bytes);
  }
  return count;
}
