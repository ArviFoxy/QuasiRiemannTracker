import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import { mkdirSync, mkdtempSync, rmSync, writeFileSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  formatBytes,
  formatCount,
  formatDuration,
  measures,
  sizeEntry,
  validateMetrics,
} from "../core/proof-size.mjs";
import { buildSizes } from "../scripts/proof-sizes.mjs";

const tree = "a".repeat(40);
const metrics = (overrides = {}) => ({
  schema_version: 1,
  result_id: "example-result",
  source_tree: tree,
  dependency_trees: {
    "example-result": tree,
    "openai-baseline": "b".repeat(40),
  },
  profile: "profile0001",
  modules: 120,
  lines: 4800,
  bytes: 190000,
  active_bytes: 150000,
  gzip_bytes: 31000,
  compile: {
    cpu_seconds: 100.5,
    cpu_seconds_by_submission: {
      "example-result": 40.25,
      "openai-baseline": 60.25,
    },
    gross_cpu_seconds: 700,
    peak_rss_bytes: 5 * 2 ** 30,
    heaviest_module: { name: "Candidate.Main", cpu_seconds: 12 },
  },
  ...overrides,
});

test("metrics describe a proof's sources and, once measured, its compile cost", () => {
  assert.equal(validateMetrics(metrics()).result_id, "example-result");
  const { compile, ...sourceOnly } = metrics();
  assert.equal(validateMetrics(sourceOnly).modules, 120);
  // Files from before the compressed size was recorded stay valid.
  const { gzip_bytes, active_bytes, ...older } = metrics();
  assert.equal(validateMetrics(older).modules, 120);
});

test("malformed metrics are rejected", () => {
  const bad = [
    { schema_version: 2 },
    { result_id: "Not Valid" },
    { source_tree: "abc" },
    { profile: undefined },
    { dependency_trees: { x: "nope" } },
    { modules: -1 },
    { lines: 1.5 },
    { bytes: "12" },
    { gzip_bytes: -1 },
    { active_bytes: 1.5 },
    { compile: { ...metrics().compile, cpu_seconds: -3 } },
    { compile: { ...metrics().compile, cpu_seconds: Infinity } },
    { compile: { ...metrics().compile, peak_rss_bytes: 1.5 } },
    { compile: { ...metrics().compile, cpu_seconds: 5000 } },
    {
      compile: { ...metrics().compile, cpu_seconds_by_submission: { a: "x" } },
    },
  ];
  for (const overrides of bad)
    assert.throws(
      () => validateMetrics(metrics(overrides)),
      /Invalid proof metrics/,
    );
});

test("the site entry separates the OpenAI baseline from what a proof adds", () => {
  assert.deepEqual(sizeEntry(metrics()), {
    modules: 120,
    lines: 4800,
    active_bytes: 150000,
    gzip_bytes: 31000,
    cpu_seconds: 100.5,
    cpu_seconds_excluding_baseline: 40.3,
    peak_rss_bytes: 5 * 2 ** 30,
  });
  const { compile, ...sourceOnly } = metrics();
  assert.deepEqual(sizeEntry(sourceOnly), {
    modules: 120,
    lines: 4800,
    active_bytes: 150000,
    gzip_bytes: 31000,
  });
  const standalone = metrics({
    compile: {
      ...metrics().compile,
      cpu_seconds_by_submission: { "example-result": 100.5 },
    },
  });
  assert.equal(sizeEntry(standalone).cpu_seconds_excluding_baseline, 100.5);
});

test("measures read their value from a site entry and say when it is missing", () => {
  const entry = sizeEntry(metrics());
  const values = Object.fromEntries(
    measures.map((m) => [m.id, m.value(entry)]),
  );
  assert.deepEqual(values, {
    cpu: 100.5,
    "cpu-own": 40.3,
    gzip: 31000,
    active: 150000,
    memory: 5 * 2 ** 30,
    modules: 120,
    lines: 4800,
  });
  const unmeasured = sizeEntry({ ...metrics(), compile: undefined });
  assert.equal(
    measures.find((m) => m.id === "cpu").value(unmeasured),
    undefined,
  );
});

test("sizes read as durations, bytes and counts", () => {
  assert.deepEqual(
    [42, 600, 3000, 3599, 3600, 5400, 9000, 36000, 400000].map(formatDuration),
    [
      "42 s",
      "10 min",
      "50 min",
      "1 h",
      "1 h",
      "1.5 h",
      "2.5 h",
      "10 h",
      "111 h",
    ],
  );
  assert.deepEqual(
    [900, 31000, 1.5 * 2 ** 20, 5.25 * 2 ** 30].map(formatBytes),
    ["0.9 KiB", "30.3 KiB", "1.5 MiB", "5.3 GiB"],
  );
  assert.deepEqual([950, 8300, 1200000].map(formatCount), [
    "950",
    "8.3K",
    "1.2M",
  ]);
});

test("the site file keeps measurements of the sources in the repository and drops stale ones", () => {
  const root = mkdtempSync(join(tmpdir(), "qrh-sizes-"));
  try {
    const git = (...args) =>
      execFileSync(
        "git",
        [
          "-C",
          root,
          "-c",
          "user.name=t",
          "-c",
          "user.email=t@example.com",
          ...args,
        ],
        { encoding: "utf8" },
      ).trim();
    git("init", "-q");
    for (const id of ["example-result", "stale-result"]) {
      mkdirSync(join(root, "submissions", id, "src/Candidate"), {
        recursive: true,
      });
      writeFileSync(
        join(root, "submissions", id, "src/Candidate/Main.lean"),
        `-- ${id}\n`,
      );
    }
    git("add", ".");
    git("commit", "-q", "-m", "sources");
    const current = git("rev-parse", "HEAD:submissions/example-result/src");
    mkdirSync(join(root, "metrics"));
    const write = (name, value) =>
      writeFileSync(join(root, "metrics", name), JSON.stringify(value));
    write("profile.json", {
      id: "profile0001",
      lean_version: "4.34.1",
      machine: { cpu: "x", cores: 4, memory_bytes: 1 },
      workers: 3,
      noise: {},
      modules_measured: 2,
    });
    write("example-result.json", metrics({ source_tree: current }));
    write(
      "stale-result.json",
      metrics({ result_id: "stale-result", source_tree: tree }),
    );
    const stale = [];
    const sizes = buildSizes(root, {
      onStale: (message) => stale.push(message),
    });
    assert.deepEqual(Object.keys(sizes.entries), ["example-result"]);
    assert.equal(sizes.profile.id, "profile0001");
    assert.deepEqual(stale, ["Ignoring stale proof metrics: stale-result"]);

    write(
      "other.json",
      metrics({
        source_tree: current,
        profile: "profile0002",
        result_id: "other",
      }),
    );
    assert.throws(() => buildSizes(root, { onStale() {} }), /another profile/);
    rmSync(join(root, "metrics/other.json"));
    write("misnamed.json", metrics({ source_tree: current }));
    assert.throws(
      () => buildSizes(root, { onStale() {} }),
      /file name differs/,
    );
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});

test("without measurements the site file is empty rather than missing", () => {
  const root = mkdtempSync(join(tmpdir(), "qrh-sizes-"));
  try {
    assert.deepEqual(buildSizes(root), { schema_version: 1, entries: {} });
  } finally {
    rmSync(root, { recursive: true, force: true });
  }
});
