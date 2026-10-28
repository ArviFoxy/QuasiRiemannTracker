import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import {
  copyFileSync,
  existsSync,
  mkdirSync,
  mkdtempSync,
  readFileSync,
  rmSync,
  symlinkSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { fileURLToPath } from "node:url";
import test from "node:test";
import {
  scanTrace,
  traceContents,
  metadataDirectory,
  validatePRTraces,
} from "../verifier/agent-traces.mjs";
import { maxMetadataBytes } from "../verifier/submission-metadata.mjs";

const folder = "2026-10-28-example-bound";
const metadataPath = `submissions/${folder}/metadata.json`;
const marker = "PRIVATE_TRACE_CONTENT_MUST_NOT_BE_PRINTED";
const cli = fileURLToPath(
  new URL("../scripts/check-agent-traces.mjs", import.meta.url),
);
const embedded = (...traces) =>
  Buffer.from(JSON.stringify({ agent_traces: traces }));

function temporary(t) {
  const root = mkdtempSync(join(tmpdir(), "qrh-trace-test-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  return root;
}

function scanner(t, exitCode = 0) {
  const root = temporary(t);
  const executable = join(root, "scanner.cjs");
  const capture = join(root, "capture.json");
  writeFileSync(
    executable,
    `#!${process.execPath}
const fs = require("node:fs");
const path = require("node:path");
const directory = process.argv.at(-1);
const files = Object.fromEntries(fs.readdirSync(directory).map(name => [name, {
  content: fs.readFileSync(path.join(directory, name), "utf8"),
  mode: fs.statSync(path.join(directory, name)).mode & 0o777
}]));
fs.writeFileSync(${JSON.stringify(capture)}, JSON.stringify({ directory, cwd: process.cwd(), argv: process.argv.slice(2), env: process.env, files }));
process.stdout.write(${JSON.stringify(marker)});
process.stderr.write(${JSON.stringify(marker)});
process.exit(${exitCode});
`,
    { mode: 0o700 },
  );
  return { executable, capture };
}

function withEnvironment(values, action) {
  const old = Object.fromEntries(
    Object.keys(values).map((key) => [key, process.env[key]]),
  );
  Object.assign(process.env, values);
  try {
    return action();
  } finally {
    for (const [key, value] of Object.entries(old)) {
      if (value === undefined) delete process.env[key];
      else process.env[key] = value;
    }
  }
}

function fixture() {
  const id = (n) => n.toString(16).padStart(40, "0");
  const ids = {
    head: id(1),
    submissions: id(2),
    folder: id(3),
    metadata: id(4),
  };
  const prefix = "repos/owner/repository/git/";
  const directory = (path, sha) => ({
    path,
    sha,
    mode: "040000",
    type: "tree",
  });
  const bytes = embedded({ message: "proof checked" });
  const entry = {
    path: "metadata.json",
    sha: ids.metadata,
    mode: "100644",
    type: "blob",
    size: bytes.length,
  };
  const blob = {
    size: bytes.length,
    encoding: "base64",
    content: bytes.toString("base64"),
  };
  const responses = new Map([
    [
      `${prefix}trees/${ids.head}`,
      { tree: [directory("submissions", ids.submissions)] },
    ],
    [
      `${prefix}trees/${ids.submissions}`,
      { tree: [directory(folder, ids.folder)] },
    ],
    [`${prefix}trees/${ids.folder}`, { tree: [entry] }],
    [`${prefix}blobs/${ids.metadata}`, blob],
  ]);
  const requests = [],
    scans = [];
  const files = [{ filename: metadataPath, status: "added" }];
  const tree = (name) => responses.get(`${prefix}trees/${ids[name]}`);
  const options = {
    repository: "owner/repository",
    pr: {
      head: {
        sha: ids.head,
        ref: "untrusted-branch",
        repo: { full_name: "fork/repository" },
      },
    },
    files,
    request: async (path) => {
      requests.push(path);
      assert.ok(responses.has(path), `Unexpected request: ${path}`);
      return structuredClone(responses.get(path));
    },
    scan: (path, bytes) => {
      scans.push({ path, bytes });
      return 1;
    },
  };
  return { options, requests, scans, tree, entry, blob, ids, files, prefix };
}

test("CI installer failures are scanner errors, while scanner exit 1 remains a secret finding", (t) => {
  const root = temporary(t);
  mkdirSync(join(root, "scripts"));
  mkdirSync(join(root, "bin"));
  const wrapper = join(root, "scripts/gitleaks.sh");
  copyFileSync(new URL("../scripts/gitleaks.sh", import.meta.url), wrapper);
  for (const [name, code] of [
    ["curl", 0],
    ["sha256sum", 1],
  ])
    writeFileSync(join(root, "bin", name), `#!/bin/sh\nexit ${code}\n`, {
      mode: 0o700,
    });
  withEnvironment(
    { QRH_GITLEAKS: wrapper, PATH: `${join(root, "bin")}:${process.env.PATH}` },
    () => {
      assert.throws(
        () => scanTrace(metadataPath, embedded({})),
        /secret scan could not complete/,
      );
      const cache = join(root, ".work/trace-gitleaks-8.30.1");
      writeFileSync(join(cache, "gitleaks"), "#!/bin/sh\nexit 1\n", {
        mode: 0o700,
      });
      assert.throws(
        () => scanTrace(metadataPath, embedded({})),
        /Possible secret/,
      );
    },
  );
});

test("embedded ATIF and native objects/arrays are accepted without a second trace schema", () => {
  const traces = [
    {
      agent: "native-export",
      events: [{ role: "assistant", text: "checked" }],
    },
    [{ role: "user", content: "prove the bound" }],
    {
      schema_version: "ATIF-v1.7",
      session_id: "session-1",
      agent: { name: "example", version: "1.0" },
      steps: [],
    },
  ];
  const result = traceContents(metadataPath, embedded(...traces));
  assert.equal(result.count, 3);
  assert.deepEqual(JSON.parse(result.raw).agent_traces, traces);
});

test("metadata parsing errors never include trace content", () => {
  for (const bytes of [
    Buffer.from(`{"agent_traces":[{"text":"${marker}"`),
    Buffer.from(`"${marker}"`),
    Buffer.from("null"),
    Buffer.from("[]"),
    Buffer.from([0xc3, 0x28]),
  ]) {
    assert.throws(
      () => traceContents(metadataPath, bytes),
      (error) => {
        assert.match(
          error.message,
          /valid UTF-8 JSON|Invalid submission metadata/,
        );
        assert.ok(!error.message.includes(marker));
        return true;
      },
    );
  }
});

test("escaped JSON keys, values and tool newlines retain scannable context", () => {
  const raw =
    '{"agent_traces":[{"api\\u005fkey":"abc\\u002d123","tool":{"output":"first\\nsecond"},"nested":[{"credential\\u005fname":"value"}]}]}';
  const result = traceContents(metadataPath, Buffer.from(raw));
  assert.equal(result.raw, raw);
  assert.match(result.decoded, /api_key: abc-123/);
  assert.match(result.decoded, /output: first\nsecond/);
  assert.match(result.decoded, /credential_name: value/);
});

test("only submission metadata is selected, including historical submission IDs", () => {
  assert.equal(metadataDirectory(metadataPath), folder);
  assert.equal(
    metadataDirectory("submissions/example-bound/metadata.json"),
    "example-bound",
  );
  for (const path of [
    "README.md",
    `submissions/${folder}/run.json`,
    `submissions/${folder}/nested/metadata.json`,
    "submissions/../metadata.json",
    `${metadataPath}\n`,
    `/${metadataPath}`,
  ])
    assert.equal(metadataDirectory(path), null, path);
});

test("raw metadata size is bounded before parsing", () => {
  assert.throws(() => traceContents(metadataPath, Buffer.alloc(0)), /nonempty/);
  assert.throws(
    () => traceContents(metadataPath, Buffer.alloc(maxMetadataBytes + 1)),
    /at most 2 MiB/,
  );
});

test("changed metadata is read from immutable head trees and blobs", async () => {
  const data = fixture();
  assert.equal(await validatePRTraces(data.options), 1);
  assert.deepEqual(data.scans, [
    { path: metadataPath, bytes: embedded({ message: "proof checked" }) },
  ]);
  assert.equal(data.requests[0], `${data.prefix}trees/${data.ids.head}`);
  assert.ok(
    data.requests.every((path) =>
      /^repos\/owner\/repository\/git\/(trees|blobs)\/[a-f0-9]{40}$/.test(path),
    ),
  );
});

test("unmodified or removed metadata needs no API calls or scanner", async () => {
  const data = fixture();
  data.options.files = [
    { filename: "README.md" },
    { filename: metadataPath, status: "removed" },
  ];
  assert.equal(await validatePRTraces(data.options), 0);
  assert.deepEqual(data.requests, []);
  assert.deepEqual(data.scans, []);
});

test("metadata renames scan the destination blob", async () => {
  const data = fixture();
  data.files[0].status = "renamed";
  data.files[0].previous_filename = "submissions/other-bound/metadata.json";
  assert.equal(await validatePRTraces(data.options), 1);
  assert.equal(data.scans[0].path, metadataPath);
});

test("invalid PR identities fail before API calls", async () => {
  for (const mutate of [
    (d) => {
      d.options.repository = "owner/repo/../other";
    },
    (d) => {
      d.options.pr.head.sha = "main";
    },
  ]) {
    const data = fixture();
    mutate(data);
    await assert.rejects(
      validatePRTraces(data.options),
      /Invalid agent trace PR identity/,
    );
    assert.deepEqual(data.requests, []);
  }
});

test("changed metadata and its parent directories must exist and be regular", async () => {
  for (const name of ["head", "submissions", "folder"]) {
    for (const patch of [
      null,
      { mode: "120000", type: "blob" },
      { sha: "main" },
    ]) {
      const data = fixture();
      if (patch) Object.assign(data.tree(name).tree[0], patch);
      else data.tree(name).tree = [];
      await assert.rejects(
        validatePRTraces(data.options),
        /Expected a regular/,
      );
      assert.deepEqual(data.scans, []);
    }
  }
});

test("truncated or duplicate trees fail closed", async () => {
  for (const name of ["head", "submissions", "folder"]) {
    for (const ambiguous of [false, true]) {
      const data = fixture();
      if (ambiguous) data.tree(name).tree.push({ ...data.tree(name).tree[0] });
      else data.tree(name).truncated = true;
      await assert.rejects(
        validatePRTraces(data.options),
        /Incomplete or ambiguous/,
      );
      assert.deepEqual(data.scans, []);
    }
  }
});

test("oversized or invalid blob lengths fail before downloading metadata", async () => {
  for (const size of [0, -1, 1.5, undefined, maxMetadataBytes + 1]) {
    const data = fixture();
    data.entry.size = size;
    await assert.rejects(
      validatePRTraces(data.options),
      /nonempty and at most 2 MiB/,
    );
    assert.ok(data.requests.every((path) => !path.includes("/blobs/")));
  }
});

test("blob encoding and declared and decoded lengths must agree", async () => {
  for (const patch of [
    { encoding: "utf-8" },
    { size: 12345 },
    { content: "e30=" },
    { content: null },
  ]) {
    const data = fixture();
    Object.assign(data.blob, patch);
    await assert.rejects(validatePRTraces(data.options), /metadata blob/);
    assert.deepEqual(data.scans, []);
  }
});

test("scanner gets embedded content in protected files without inherited credentials", (t) => {
  const fake = scanner(t);
  const bytes = embedded({ api_key: "abc-123", comment: "gitleaks:allow" });
  withEnvironment(
    {
      QRH_GITLEAKS: fake.executable,
      GITHUB_TOKEN: marker,
      GH_TOKEN: marker,
      OPENAI_API_KEY: marker,
      GITLEAKS_CONFIG: "/untrusted/rules.toml",
      NODE_OPTIONS: "--no-warnings",
    },
    () => assert.equal(scanTrace(metadataPath, bytes), 1),
  );
  const capture = JSON.parse(readFileSync(fake.capture, "utf8"));
  assert.deepEqual(
    JSON.parse(capture.files["raw.json"].content),
    JSON.parse(bytes),
  );
  assert.match(capture.files["decoded.txt"].content, /api_key: abc-123/);
  assert.equal(capture.files.ignore.content, "");
  assert.match(capture.files["rules.toml"].content, /useDefault = true/);
  assert.ok(capture.argv.includes("--ignore-gitleaks-allow"));
  assert.ok(capture.argv.includes("--redact=100"));
  assert.equal(capture.cwd, capture.directory);
  assert.deepEqual(Object.keys(capture.env), ["PATH"]);
  assert.ok(Object.values(capture.files).every((file) => file.mode === 0o600));
  assert.ok(!existsSync(capture.directory));
});

for (const [exitCode, message] of [
  [1, /Possible secret/],
  [2, /secret scan could not complete/],
]) {
  test(`scanner failure ${exitCode} hides output and removes temporary files`, (t) => {
    const fake = scanner(t, exitCode);
    withEnvironment({ QRH_GITLEAKS: fake.executable }, () => {
      assert.throws(
        () => scanTrace(metadataPath, embedded({ message: "example" })),
        (error) => {
          assert.match(error.message, message);
          assert.ok(!error.message.includes(marker));
          return true;
        },
      );
    });
    const capture = JSON.parse(readFileSync(fake.capture, "utf8"));
    assert.ok(!existsSync(capture.directory));
  });
}

test("an unavailable scanner fails only when traces are supplied", (t) => {
  withEnvironment(
    { QRH_GITLEAKS: join(temporary(t), "does-not-exist") },
    () => {
      assert.throws(
        () => scanTrace(metadataPath, embedded({})),
        /secret scan could not complete/,
      );
      assert.equal(scanTrace(metadataPath, embedded()), 0);
      assert.equal(scanTrace(metadataPath, Buffer.from("{}")), 0);
    },
  );
});

function localFixture(t, exitCode = 0) {
  const root = temporary(t);
  mkdirSync(join(root, "submissions", folder), { recursive: true });
  writeFileSync(
    join(root, metadataPath),
    embedded({ message: "proof checked" }),
  );
  const fake = scanner(t, exitCode);
  const run = (...args) =>
    spawnSync(process.execPath, [cli, ...args], {
      cwd: root,
      encoding: "utf8",
      env: { ...process.env, QRH_GITLEAKS: fake.executable },
    });
  return { root, run };
}

test("local command checks selected or all submission metadata without exposing scanner output", (t) => {
  const data = localFixture(t);
  for (const args of [[metadataPath], []]) {
    const result = data.run(...args);
    assert.equal(result.status, 0, result.stderr);
    assert.match(result.stdout, /1 embedded exports checked/);
    assert.ok(!result.stdout.includes(marker));
    assert.equal(result.stderr, "");
  }
});

for (const [exitCode, message] of [
  [1, /Possible secret/],
  [2, /secret scan could not complete/],
]) {
  test(`local command suppresses scanner output on failure ${exitCode}`, (t) => {
    const result = localFixture(t, exitCode).run(metadataPath);
    assert.equal(result.status, 1);
    assert.match(result.stderr, message);
    assert.ok(!result.stdout.includes(marker));
    assert.ok(!result.stderr.includes(marker));
  });
}

test("local command rejects symlink submission roots, directories and metadata", (t) => {
  for (const path of ["submissions", `submissions/${folder}`, metadataPath]) {
    const data = localFixture(t);
    const target = join(temporary(t), "target");
    const original = join(data.root, path);
    if (path.endsWith(".json")) writeFileSync(target, embedded({}));
    else mkdirSync(target);
    rmSync(original, { recursive: true, force: true });
    symlinkSync(target, original);
    const result = data.run(metadataPath);
    assert.equal(result.status, 1);
    assert.match(result.stderr, /regular/);
  }
});

test("local command needs no installed scanner without embedded traces", (t) => {
  const data = localFixture(t);
  writeFileSync(join(data.root, metadataPath), '{"agent_traces":[]}');
  const result = spawnSync(process.execPath, [cli], {
    cwd: data.root,
    encoding: "utf8",
    env: { ...process.env, QRH_GITLEAKS: "/not-installed/gitleaks" },
  });
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /0 embedded exports checked/);
});

test("historical metadata with an executable bit is read only as JSON", async (t) => {
  const data = fixture();
  data.entry.mode = "100755";
  assert.equal(await validatePRTraces(data.options), 1);
  const local = localFixture(t);
  const { chmodSync } = await import("node:fs");
  chmodSync(join(local.root, metadataPath), 0o755);
  const result = local.run(metadataPath);
  assert.equal(result.status, 0, result.stderr);
});
