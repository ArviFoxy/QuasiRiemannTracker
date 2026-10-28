import assert from "node:assert/strict";
import { spawnSync } from "node:child_process";
import {
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
  traceDirectory,
  traceLimits,
  validatePRTraces,
  validateTraceSizes,
} from "../verifier/agent-traces.mjs";

const folder = "2026-10-28-example-bound";
const tracePath = `agent-traces/${folder}/run-01.json`;
const jsonlPath = `agent-traces/${folder}/run-01.jsonl`;
const marker = "PRIVATE_TRACE_CONTENT_MUST_NOT_BE_PRINTED";
const cli = fileURLToPath(
  new URL("../scripts/check-agent-traces.mjs", import.meta.url),
);

function temporary(t) {
  const root = mkdtempSync(join(tmpdir(), "qrh-trace-test-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  return root;
}

function fixture() {
  const id = (n) => n.toString(16).padStart(40, "0");
  const ids = { head: id(1), traces: id(2), submissions: id(3), folder: id(4) };
  const prefix = "repos/owner/repository/git/";
  const directory = (path, sha) => ({
    path,
    sha,
    mode: "040000",
    type: "tree",
  });
  const responses = new Map([
    [
      `${prefix}trees/${ids.head}`,
      {
        tree: [
          directory("agent-traces", ids.traces),
          directory("submissions", ids.submissions),
        ],
      },
    ],
    [`${prefix}trees/${ids.traces}`, { tree: [directory(folder, ids.folder)] }],
    [`${prefix}trees/${ids.submissions}`, { tree: [directory(folder, id(5))] }],
    [`${prefix}trees/${ids.folder}`, { tree: [] }],
  ]);
  const requests = [],
    scans = [];
  const files = [{ filename: tracePath, status: "added" }];
  const tree = (name) => responses.get(`${prefix}trees/${ids[name]}`);
  let nextBlob = 10;
  function addFile(
    path = "run-01.json",
    content = '{"message":"proof checked"}',
  ) {
    const bytes = Buffer.from(content);
    const entry = {
      path,
      sha: id(nextBlob++),
      mode: "100644",
      type: "blob",
      size: bytes.length,
    };
    tree("folder").tree.push(entry);
    const blob = {
      size: bytes.length,
      encoding: "base64",
      content: bytes.toString("base64"),
    };
    responses.set(`${prefix}blobs/${entry.sha}`, blob);
    return { entry, blob };
  }
  const first = addFile();
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
    scan: (path, bytes) => scans.push({ path, bytes }),
  };
  return {
    options,
    requests,
    scans,
    tree,
    addFile,
    first,
    ids,
    files,
    responses,
    prefix,
  };
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

test("native JSON objects, arrays and ATIF exports remain accepted without inventing a schema", () => {
  for (const value of [
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
  ]) {
    const raw = JSON.stringify(value);
    assert.equal(traceContents(tracePath, Buffer.from(raw)).raw, raw);
  }
});

test("JSONL accepts object records and blank lines but rejects arrays and scalar records", () => {
  const raw = '\n{"event":"start"}\r\n  \n{"event":"end"}\n';
  assert.equal(traceContents(jsonlPath, Buffer.from(raw)).raw, raw);
  for (const bad of [
    "[]\n",
    "null\n",
    "true\n",
    "1\n",
    '"message"\n',
    "{}\n[]\n",
    " \n\t",
  ]) {
    assert.throws(
      () => traceContents(jsonlPath, Buffer.from(bad)),
      /Invalid UTF-8 JSON/,
    );
  }
});

test("JSON and UTF-8 errors never include source content", () => {
  for (const bytes of [
    Buffer.from(`{"message":"${marker}"`),
    Buffer.from(`"${marker}"`),
    Buffer.from("null"),
    Buffer.from("123"),
    Buffer.from("false"),
    Buffer.from([0xc3, 0x28]),
  ]) {
    assert.throws(
      () => traceContents(tracePath, bytes),
      (error) => {
        assert.match(error.message, /Invalid UTF-8 JSON/);
        assert.ok(!error.message.includes(marker));
        return true;
      },
    );
  }
});

test("JSON-unescaped strings, keys and tool output retain scannable context", () => {
  const raw =
    '{"api\\u005fkey":"abc\\u002d123","tool":{"output":"first\\nsecond"},"nested":[{"credential\\u005fname":"value"}]}';
  const result = traceContents(tracePath, Buffer.from(raw));
  assert.equal(result.raw, raw);
  assert.match(result.decoded, /api_key: abc-123/);
  assert.match(result.decoded, /output: first\nsecond/);
  assert.match(result.decoded, /credential_name: value/);
});

test("trace paths require one valid date, flat regular filenames and JSON extensions", () => {
  assert.equal(traceDirectory(tracePath), folder);
  assert.equal(traceDirectory(jsonlPath), folder);
  for (const path of [
    "agent-traces",
    "agent-traces/README.md",
    "agent-traces/example-bound/run.json",
    "agent-traces/2026-02-30-example-bound/run.json",
    "agent-traces/2026-10-28-example-2026-10-27/run.json",
    `agent-traces/${folder}/../run.json`,
    `agent-traces/${folder}/nested/run.json`,
    `agent-traces/${folder}/.run.json`,
    `agent-traces/${folder}/run.txt`,
    `agent-traces/${folder}/run.JSON`,
    `agent-traces/${folder}/run name.json`,
    `agent-traces/${folder}/${"a".repeat(101)}.json`,
    `agent-traces/${folder}/run.json\n`,
    `/agent-traces/${folder}/run.json`,
    `agent-traces\\${folder}\\run.json`,
  ])
    assert.equal(traceDirectory(path), null, path);
});

test("per-file and aggregate limits are bounded before parsing or fetching blobs", () => {
  assert.throws(() => traceContents(tracePath, Buffer.alloc(0)), /nonempty/);
  assert.throws(
    () => traceContents(tracePath, Buffer.alloc(traceLimits.fileBytes + 1)),
    /at most 10 MiB/,
  );
  assert.doesNotThrow(() =>
    validateTraceSizes(Array.from({ length: 50 }, () => ({ size: 1 }))),
  );
  assert.doesNotThrow(() =>
    validateTraceSizes(
      Array.from({ length: 5 }, () => ({ size: traceLimits.fileBytes })),
    ),
  );
  for (const files of [
    [{ size: 0 }],
    [{ size: -1 }],
    [{ size: 1.5 }],
    [{ size: NaN }],
    [{ size: Infinity }],
    [{}],
    [{ size: traceLimits.fileBytes + 1 }],
    Array.from({ length: 51 }, () => ({ size: 1 })),
    [
      ...Array.from({ length: 5 }, () => ({ size: traceLimits.fileBytes })),
      { size: 1 },
    ],
  ])
    assert.throws(() => validateTraceSizes(files), /size limit/);
});

test("a PR reads immutable head trees and scans every file in each touched folder", async () => {
  const data = fixture();
  const second = data.addFile("older-run.jsonl", '{"older":true}\n');
  assert.equal(await validatePRTraces(data.options), 2);
  assert.deepEqual(
    data.scans.map((scan) => scan.path),
    [tracePath, `agent-traces/${folder}/${second.entry.path}`],
  );
  assert.equal(data.scans[0].bytes.toString(), '{"message":"proof checked"}');
  assert.equal(data.requests[0], `${data.prefix}trees/${data.ids.head}`);
  assert.ok(
    data.requests.every((path) =>
      /^repos\/owner\/repository\/git\/(trees|blobs)\/[a-f0-9]{40}$/.test(path),
    ),
  );
});

test("unchanged traces and the trace README need no API or scanner", async () => {
  const data = fixture();
  data.options.files = [
    { filename: "README.md" },
    { filename: "agent-traces/README.md" },
  ];
  assert.equal(await validatePRTraces(data.options), 0);
  assert.deepEqual(data.requests, []);
  assert.deepEqual(data.scans, []);
});

test("removing the last trace or a whole trace folder requires no scanner", async () => {
  for (const wholeRoot of [false, true]) {
    const data = fixture();
    data.files[0].status = "removed";
    if (wholeRoot) data.tree("head").tree = [];
    else data.tree("traces").tree = [];
    assert.equal(await validatePRTraces(data.options), 0);
    assert.deepEqual(data.scans, []);
  }
});

test("renames validate the previous trace folder as well as the new path", async () => {
  const data = fixture();
  data.options.files = [
    { filename: "notes.json", previous_filename: tracePath, status: "renamed" },
  ];
  assert.equal(await validatePRTraces(data.options), 1);
  assert.equal(data.scans[0].path, tracePath);
});

test("invalid PR identities and unsupported trace paths fail before any API calls", async () => {
  for (const mutate of [
    (data) => {
      data.options.repository = "owner/repo/../other";
    },
    (data) => {
      data.options.pr.head.sha = "main";
    },
    (data) => {
      data.files[0].filename = `agent-traces/${folder}/run.sh`;
    },
  ]) {
    const data = fixture();
    mutate(data);
    await assert.rejects(
      validatePRTraces(data.options),
      /Invalid agent trace PR identity|Agent traces must use/,
    );
    assert.deepEqual(data.requests, []);
  }
});

test("a changed trace must exist at the immutable head and have a matching submission", async () => {
  for (const [mutate, message] of [
    [
      (data) => {
        data.tree("head").tree = data
          .tree("head")
          .tree.filter((entry) => entry.path !== "agent-traces");
      },
      /missing from the PR head/,
    ],
    [
      (data) => {
        data.tree("traces").tree = [];
      },
      /missing from the PR head/,
    ],
    [
      (data) => {
        data.first.entry.path = "other-run.json";
      },
      /missing from the PR head/,
    ],
    [
      (data) => {
        data.tree("submissions").tree = [];
      },
      /existing submission directory/,
    ],
    [
      (data) => {
        data.tree("head").tree = data
          .tree("head")
          .tree.filter((entry) => entry.path !== "submissions");
      },
      /existing submission directory/,
    ],
  ]) {
    const data = fixture();
    mutate(data);
    await assert.rejects(validatePRTraces(data.options), message);
    assert.deepEqual(data.scans, []);
  }
});

test("trace and submission directories cannot be symlinks or non-tree entries", async () => {
  for (const [treeName, index] of [
    ["head", 0],
    ["head", 1],
    ["traces", 0],
    ["submissions", 0],
  ]) {
    const data = fixture();
    Object.assign(data.tree(treeName).tree[index], {
      mode: "120000",
      type: "blob",
    });
    await assert.rejects(
      validatePRTraces(data.options),
      /regular agent trace\/submission directory/,
    );
    assert.deepEqual(data.scans, []);
  }
});

test("trace blobs cannot be executable, symlinks, nested directories or unsupported files", async () => {
  for (const patch of [
    { mode: "100755" },
    { mode: "120000" },
    { type: "tree", mode: "040000" },
    { path: "nested/run.json" },
    { path: "gitleaks.toml" },
    { sha: "main" },
  ]) {
    const data = fixture();
    data.addFile("other.json");
    Object.assign(data.tree("folder").tree[1], patch);
    await assert.rejects(
      validatePRTraces(data.options),
      /regular JSON\/JSONL files/,
    );
    assert.deepEqual(data.scans, []);
  }
});

test("limits apply to unchanged files in a touched folder before downloading any blob", async () => {
  for (const mode of ["count", "total", "file"]) {
    const data = fixture();
    if (mode === "count")
      for (let n = 0; n < 50; n++) data.addFile(`older-${n}.json`);
    if (mode === "total")
      for (let n = 0; n < 5; n++)
        data.addFile(`older-${n}.json`).entry.size = traceLimits.fileBytes;
    if (mode === "file")
      data.addFile("older.json").entry.size = traceLimits.fileBytes + 1;
    await assert.rejects(validatePRTraces(data.options), /size limit/);
    assert.ok(data.requests.every((path) => !path.includes("/blobs/")));
    assert.deepEqual(data.scans, []);
  }
});

test("truncated and duplicate Git trees cannot silently omit traces", async () => {
  for (const name of ["head", "traces", "submissions", "folder"]) {
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

test("blob encoding and both advertised and decoded sizes must agree", async () => {
  for (const [patch, message] of [
    [{ encoding: "utf-8" }, /Invalid agent trace blob/],
    [{ size: 12345 }, /Invalid agent trace blob/],
    [{ content: "e30=" }, /blob size mismatch/],
    [{ content: null }, /Invalid agent trace blob/],
  ]) {
    const data = fixture();
    Object.assign(data.first.blob, patch);
    await assert.rejects(validatePRTraces(data.options), message);
    assert.deepEqual(data.scans, []);
  }
});

test("scanner receives raw and decoded content with protected files and no inherited credentials", (t) => {
  const fake = scanner(t);
  const raw = '{"api\\u005fkey":"abc\\u002d123","comment":"gitleaks:allow"}';
  withEnvironment(
    {
      QRH_GITLEAKS: fake.executable,
      GITHUB_TOKEN: marker,
      GH_TOKEN: marker,
      OPENAI_API_KEY: marker,
      GITLEAKS_CONFIG: "/untrusted/rules.toml",
      NODE_OPTIONS: "--no-warnings",
    },
    () => scanTrace(tracePath, Buffer.from(raw)),
  );
  const capture = JSON.parse(readFileSync(fake.capture, "utf8"));
  assert.equal(capture.files["raw.json"].content, raw);
  assert.match(capture.files["decoded.txt"].content, /api_key: abc-123/);
  assert.equal(capture.files["ignore"].content, "");
  assert.match(capture.files["rules.toml"].content, /useDefault = true/);
  assert.ok(capture.argv.includes("--ignore-gitleaks-allow"));
  assert.ok(capture.argv.includes("--redact=100"));
  assert.equal(capture.env.HOME, capture.directory);
  assert.equal(capture.cwd, capture.directory);
  assert.deepEqual(Object.keys(capture.env).sort(), ["HOME", "PATH"]);
  assert.ok(Object.values(capture.files).every((file) => file.mode === 0o600));
  assert.ok(
    !existsSync(capture.directory),
    "scanner workspace must be removed",
  );
});

for (const [exitCode, message] of [
  [1, /Possible secret/],
  [2, /secret scan could not complete/],
]) {
  test(`scanner failure ${exitCode} hides all output and removes its temporary files`, (t) => {
    const fake = scanner(t, exitCode);
    withEnvironment({ QRH_GITLEAKS: fake.executable }, () => {
      assert.throws(
        () => scanTrace(tracePath, Buffer.from('{"message":"example"}')),
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

test("an unavailable scanner fails closed", (t) => {
  withEnvironment(
    { QRH_GITLEAKS: join(temporary(t), "does-not-exist") },
    () => {
      assert.throws(
        () => scanTrace(tracePath, Buffer.from("{}")),
        /secret scan could not complete/,
      );
    },
  );
});

function localFixture(t, exitCode = 0) {
  const root = temporary(t);
  mkdirSync(join(root, "agent-traces", folder), { recursive: true });
  mkdirSync(join(root, "submissions", folder), { recursive: true });
  writeFileSync(join(root, tracePath), '{"message":"proof checked"}');
  const fake = scanner(t, exitCode);
  const run = (...args) =>
    spawnSync(process.execPath, [cli, ...args], {
      cwd: root,
      encoding: "utf8",
      env: { ...process.env, QRH_GITLEAKS: fake.executable },
    });
  return { root, run };
}

test("local command checks a selected submission folder and suppresses scanner output", (t) => {
  const data = localFixture(t);
  const result = data.run(`agent-traces/${folder}`);
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /1 files checked/);
  assert.ok(!result.stdout.includes(marker));
  assert.equal(result.stderr, "");
});

for (const [exitCode, message] of [
  [1, /Possible secret/],
  [2, /secret scan could not complete/],
]) {
  test(`local command suppresses scanner stdout and stderr on failure ${exitCode}`, (t) => {
    const data = localFixture(t, exitCode);
    const result = data.run(`agent-traces/${folder}`);
    assert.equal(result.status, 1);
    assert.match(result.stderr, message);
    assert.ok(!result.stdout.includes(marker));
    assert.ok(!result.stderr.includes(marker));
  });
}

test("local command rejects symlink trace roots, folders and files", (t) => {
  for (const path of ["agent-traces", `agent-traces/${folder}`, tracePath]) {
    const data = localFixture(t);
    const target = join(temporary(t), "target");
    const original = join(data.root, path);
    if (path.endsWith(".json")) writeFileSync(target, "{}");
    else mkdirSync(target);
    rmSync(original, { recursive: true, force: true });
    symlinkSync(target, original);
    const result = data.run(`agent-traces/${folder}`);
    assert.equal(result.status, 1);
    assert.match(result.stderr, /regular|ENOENT/);
  }
});

test("local command succeeds without an installed scanner when no traces are present", (t) => {
  const result = spawnSync(process.execPath, [cli], {
    cwd: temporary(t),
    encoding: "utf8",
    env: { ...process.env, QRH_GITLEAKS: "/not-installed/gitleaks" },
  });
  assert.equal(result.status, 0, result.stderr);
  assert.match(result.stdout, /0 files checked/);
});
