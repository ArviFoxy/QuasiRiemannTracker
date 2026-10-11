import test from "node:test";
import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";

const repository = "GTimG/QuasiRiemannTracker";
const head = "a".repeat(40);
const entrypoint = new URL("../verifier/check-pr.mjs", import.meta.url).href;

function fixture(files = [{ filename: "README.md", status: "modified" }]) {
  return {
    pr: {
      number: 15,
      state: "open",
      draft: false,
      title: "Maintenance",
      body: "QRH-Type: maintenance",
      head: { sha: head, repo: { full_name: "Contributor/Tracker" } },
      base: {
        sha: "b".repeat(40),
        ref: "main",
        repo: { full_name: repository },
      },
      changed_files: files.length,
    },
    files,
  };
}

// This child replaces fetch before importing the executable module. Every API
// read and write is synthetic, and an unknown request fails without networking.
const harness = `
const fixture = JSON.parse(process.env.QRH_TEST_FIXTURE);
const requests = [];
let prReads = 0;
globalThis.fetch = async (url, options = {}) => {
  const request = {
    url: String(url),
    method: options.method ?? "GET",
    body: options.body ? JSON.parse(options.body) : undefined,
  };
  requests.push(request);
  const parsed = new URL(request.url);
  const route = parsed.pathname;
  if (parsed.origin !== "https://api.github.com") throw Error("Unexpected API origin");
  let value;
  if (request.method === "GET" && route === "/repos/${repository}/pulls/15") {
    value = prReads++ === 0 ? fixture.pr : (fixture.current ?? fixture.pr);
  } else if (request.method === "GET" && route === "/repos/${repository}/pulls/15/files") {
    if (parsed.searchParams.get("per_page") !== "100") throw Error("Unexpected page size");
    const page = Number(parsed.searchParams.get("page"));
    value = fixture.files.slice((page - 1) * 100, page * 100);
  } else if (request.method === "POST" && route === "/repos/${repository}/check-runs") {
    value = { id: 123 };
  } else if (request.method === "PATCH" && route === "/repos/${repository}/check-runs/123") {
    value = { id: 123 };
  } else throw Error("Unexpected API request: " + request.method + " " + request.url);
  return { ok: true, status: 200, json: async () => structuredClone(value) };
};
let importError;
try { await import(${JSON.stringify(entrypoint)}); }
catch (error) { importError = error.message; process.exitCode = 1; }
console.log("MOCK_RESULT=" + JSON.stringify({ requests, importError }));
`;

function run(t, data, overrides = {}) {
  const cwd = mkdtempSync(join(tmpdir(), "qrh-check-pr-"));
  t.after(() => rmSync(cwd, { recursive: true, force: true }));
  mkdirSync(join(cwd, "verifier"));
  writeFileSync(
    join(cwd, "verifier/pr-admissions.json"),
    JSON.stringify({ schema_version: 1, admissions: [] }),
  );
  const child = spawnSync(
    process.execPath,
    ["--input-type=module", "--eval", harness],
    {
      cwd,
      encoding: "utf8",
      timeout: 10_000,
      env: {
        GITHUB_REPOSITORY: repository,
        GITHUB_TOKEN: "synthetic-test-token",
        GITHUB_REF: "refs/heads/main",
        GITHUB_EVENT_NAME: "pull_request_target",
        GITHUB_RUN_ID: "456",
        QRH_PR: "15",
        QRH_DEFAULT_BRANCH: "main",
        QRH_TEST_FIXTURE: JSON.stringify(data),
        ...overrides,
      },
    },
  );
  assert.ifError(child.error);
  assert.equal(child.signal, null, child.stderr);
  const line = child.stdout
    .split("\n")
    .find((value) => value.startsWith("MOCK_RESULT="));
  assert.ok(line, `No mock results: ${child.stdout}\n${child.stderr}`);
  const result = JSON.parse(line.slice("MOCK_RESULT=".length));
  return {
    ...result,
    status: child.status,
    writes: result.requests.filter((request) => request.method !== "GET"),
  };
}

test("maintenance publishes qrh/pr-admission success on the current PR head", (t) => {
  const result = run(t, fixture());
  assert.equal(result.status, 0);
  assert.equal(result.importError, undefined);
  assert.equal(result.writes.length, 2);
  const [created, completed] = result.writes;
  assert.equal(created.method, "POST");
  assert.equal(created.body.name, "qrh/pr-admission");
  assert.equal(created.body.head_sha, head);
  assert.equal(created.body.status, "in_progress");
  assert.equal(completed.method, "PATCH");
  assert.equal(
    completed.url,
    `https://api.github.com/repos/${repository}/check-runs/123`,
  );
  assert.equal(completed.body.status, "completed");
  assert.equal(completed.body.conclusion, "success");
});

test("a proof on the second changed-files page prevents maintenance admission", (t) => {
  const files = Array.from({ length: 100 }, (_, i) => ({
    filename: `docs/page-${i}.md`,
    status: "modified",
  }));
  files.push({ filename: "proofs/candidate/Main.lean", status: "added" });
  const result = run(t, fixture(files));
  assert.equal(result.status, 1);
  const pages = result.requests
    .filter((request) => new URL(request.url).pathname.endsWith("/files"))
    .map((request) => new URL(request.url).searchParams.get("page"));
  assert.deepEqual(pages, ["1", "2"]);
  assert.equal(result.writes.at(-1).body.conclusion, "failure");
  assert.match(
    result.writes.at(-1).body.output.summary,
    /require QRH-Type: new-bound/,
  );
});

test("a declared new bound without trusted evidence publishes failure", (t) => {
  const data = fixture([
    { filename: "proofs/candidate/Main.lean", status: "added" },
  ]);
  data.pr.body =
    "QRH-Type: new-bound\nQRH-Result: candidate-20261011\nQRH-Bound: 4374433/5000000";
  const result = run(t, data);
  assert.equal(result.status, 1);
  assert.equal(result.writes.at(-1).body.conclusion, "failure");
  assert.match(
    result.writes.at(-1).body.output.summary,
    /no trusted verification/,
  );
});

test("a head or declaration change on the final reread prevents success", (t) => {
  for (const change of ["head", "body"]) {
    const data = fixture();
    data.current = structuredClone(data.pr);
    if (change === "head") data.current.head.sha = "c".repeat(40);
    else data.current.body = "QRH-Type: new-bound";
    const result = run(t, data);
    assert.equal(result.status, 1, change);
    assert.equal(result.writes[0].body.head_sha, head);
    assert.equal(result.writes.at(-1).body.conclusion, "failure", change);
    assert.match(
      result.writes.at(-1).body.output.summary,
      /changed during validation/,
    );
  }
});

test("a workflow running outside the default branch cannot read or publish checks", (t) => {
  const result = run(t, fixture(), {
    GITHUB_REF: "refs/heads/untrusted-candidate",
  });
  assert.equal(result.status, 1);
  assert.match(
    result.importError,
    /Trusted default-branch PR admission orchestration required/,
  );
  assert.deepEqual(result.requests, []);
  assert.deepEqual(result.writes, []);
});
