import test from "node:test";
import { canonical, sha256 } from "../verifier/common.mjs";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  existsSync,
  mkdtempSync,
  mkdirSync,
  readFileSync,
  rmSync,
  writeFileSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import {
  generateCatalogue,
  reconcileAdmissions,
} from "../scripts/reconcile-admissions.mjs";
import {
  admissionPath,
  admissionRecord,
} from "../verifier/admission-archive.mjs";
import { workerCertificate } from "../verifier/certificate.mjs";
import { recordHistory } from "../core/rational.mjs";
import { timelineRecords } from "../core/catalogue.mjs";

const repository = "owner/repository";
const hex = (character) => character.repeat(40);
const metadata = {
  title: "Contributor · an exact improvement",
  authors: [{ name: "Original Author", url: "https://example.com/author" }],
  description: "The argument and its attribution supplied by the contributor.",
  license: "Apache-2.0",
  builds_on: ["legacy-proof"],
  references: [{ label: "Paper", url: "https://example.com/paper" }],
};
const legacyRecord = () => ({
  id: "legacy-proof",
  title: "Reviewed legacy result",
  theta: { numerator: "7", denominator: "8" },
  authors: [{ name: "Legacy Author" }],
  method: "A reviewed argument.",
  license: "Apache-2.0",
  builds_on: [],
  references: [{ label: "Source", url: "https://example.com/legacy" }],
  status: "framework-verified",
  timeline_at: "2026-10-10T00:00:00Z",
  first_verified_at: "2026-10-10T00:00:00Z",
  date_label: "Verification",
  verification_note: "Independent checks passed.",
  source_commit: hex("b"),
  repository,
  certificate_url: "certificates/legacy-proof.json",
});

function fixture(t, { dated = false, dependencies = false } = {}) {
  const root = mkdtempSync(join(tmpdir(), "qrh-reconcile-"));
  t.after(() => rmSync(root, { recursive: true, force: true }));
  const git = (...args) =>
    execFileSync("git", args, {
      cwd: root,
      encoding: "utf8",
      stdio: ["ignore", "pipe", "pipe"],
    }).trim();
  const candidatePath = `submissions/${dated ? "2026-10-12-" : ""}candidate-proof`;
  const legacyPath = `submissions/${dated ? "2026-10-10-" : ""}legacy-proof`;
  const submissionMetadata = dependencies
    ? { ...metadata, dependencies: ["legacy-proof"] }
    : metadata;
  const legacy = legacyRecord();
  const writeLegacy = () => {
    mkdirSync(join(root, legacyPath, "src/Candidate"), { recursive: true });
    writeFileSync(
      join(root, legacyPath, "metadata.json"),
      JSON.stringify({
        ...legacy,
        verification: {
          report_url: `https://github.com/${repository}/actions/runs/100`,
          report_sha256: "f".repeat(64),
        },
      }),
    );
    writeFileSync(
      join(root, legacyPath, "src/Candidate/Main.lean"),
      "-- fixture source\n",
    );
  };
  if (dependencies) writeLegacy();
  mkdirSync(join(root, candidatePath, "src/Candidate"), {
    recursive: true,
  });
  writeFileSync(
    join(root, candidatePath, "src/Candidate/Main.lean"),
    "-- Source is data; reconciliation never compiles or executes it.\n",
  );
  writeFileSync(
    join(root, candidatePath, "metadata.json"),
    JSON.stringify(submissionMetadata),
  );
  git("init", "-q");
  git(
    "-c",
    "user.name=Test",
    "-c",
    "user.email=test@example.com",
    "commit",
    "--allow-empty",
    "-qm",
    "Before candidate merge",
  );
  const earlier = git("rev-parse", "HEAD");
  git("add", "submissions");
  git(
    "-c",
    "user.name=Test",
    "-c",
    "user.email=test@example.com",
    "commit",
    "-qm",
    "Source snapshot",
  );
  const head = git("rev-parse", "HEAD");
  const expected = {
    repository,
    number: 26,
    head_sha: head,
    result_id: "candidate-proof",
    theta_exact: "4/5",
  };
  const report = {
    status: "PASS",
    verified_at: "2026-10-13T00:00:00Z",
    reviewed_pr_head: head,
    source_repository: repository,
    result_id: expected.result_id,
    theta_exact: expected.theta_exact,
    judge_exit_code: 0,
    targets: ["QRH.canonical_bound"],
    kernels: ["Lean default", "nanoda", "con-ron"],
    allowed_axioms: ["propext", "Classical.choice", "Quot.sound"],
    sandbox_preflight: "PASS",
    candidate_mount_preflight: "PASS",
    challenge_exported_before_candidate_execution: true,
    receipt_outside_candidate: true,
  };
  const reportBytes = Buffer.from(JSON.stringify(report));
  const context = {
    repository,
    defaultBranch: "main",
    run_id: "1234",
    run_attempt: "1",
    workflow_sha: hex("c"),
    check_id: 1235,
  };
  const pr = {
    number: 26,
    state: "open",
    head: { sha: head },
    base: { ref: "main", repo: { full_name: repository } },
    title: "PR title is separate from authored publication metadata",
    body: `QRH-Result: candidate-proof\nQRH-Bound: 4/5\nQRH-Decimal: 0.8\n\n\`\`\`qrh-metadata\n${JSON.stringify(submissionMetadata)}\n\`\`\``,
    created_at: "2026-10-12T00:00:00Z",
    user: { login: "submitter" },
  };
  const envelope = admissionRecord({
    context,
    pr,
    expected,
    reportBytes,
    archivedAt: "2026-10-13T00:01:00Z",
    metadata: submissionMetadata,
    sourcePath: `${candidatePath}/src`,
    sourceTree: git("rev-parse", `HEAD:${candidatePath}/src`),
    dependencyTrees: dependencies
      ? { "legacy-proof": git("rev-parse", `HEAD:${legacyPath}`) }
      : {},
    record: workerCertificate(
      expected,
      report,
      `https://github.com/${repository}/actions/runs/1234/attempts/1`,
      reportBytes,
    ),
  });
  const merged = {
    ...pr,
    state: "closed",
    merged: true,
    merged_at: "2026-10-13T01:00:00Z",
    merge_commit_sha: head,
  };
  const admission = {
    ...envelope,
    merged_at: merged.merged_at,
    merge_commit_sha: merged.merge_commit_sha,
  };
  if (!dependencies) writeLegacy();
  return {
    root,
    git,
    earlier,
    legacy,
    envelope,
    admission,
    merged,
    candidatePath,
    legacyPath,
  };
}

function mockApi(
  data,
  { records = [data.envelope], pull = data.merged, overrides = {} } = {},
) {
  const routes = {
    "git/ref/heads/admission-records": { object: { sha: hex("d") } },
    [`git/commits/${hex("d")}`]: { tree: { sha: hex("e") } },
    [`git/trees/${hex("e")}?recursive=1`]: {
      truncated: false,
      tree: records.map((record, i) => ({
        path: admissionPath(record),
        mode: "100644",
        type: "blob",
        sha: hex(String(i + 1)),
        size: JSON.stringify(record).length,
      })),
    },
    ...Object.fromEntries(
      records.map((record, i) => [
        `git/blobs/${hex(String(i + 1))}`,
        {
          encoding: "base64",
          content: Buffer.from(JSON.stringify(record)).toString("base64"),
          size: JSON.stringify(record).length,
        },
      ]),
    ),
    "pulls/26": pull,
    ...overrides,
  };
  const requests = [];
  return {
    requests,
    fetcher: async (url, options) => {
      assert.equal(options.headers.Authorization, "Bearer test-token");
      assert.equal(options.method ?? "GET", "GET");
      assert.ok(url.startsWith(`https://api.github.com/repos/${repository}/`));
      const route = url.slice(
        `https://api.github.com/repos/${repository}/`.length,
      );
      requests.push(route);
      assert.ok(Object.hasOwn(routes, route), `Unexpected API route: ${route}`);
      const value = routes[route];
      return value === null
        ? { ok: false, status: 404 }
        : { ok: true, status: 200, json: async () => value };
    },
  };
}
const online = (data, api) =>
  reconcileAdmissions({
    root: data.root,
    repository,
    defaultBranch: "main",
    online: true,
    token: "test-token",
    fetcher: api.fetcher,
  });

function ancestorFixture(t, { changeHead, changeMerge } = {}) {
  const data = fixture(t, { dated: true, dependencies: true });
  data.git("config", "user.name", "Test");
  data.git("config", "user.email", "test@example.com");
  data.git("checkout", "--detach", data.earlier);
  writeFileSync(join(data.root, "README.md"), "Unrelated main maintenance\n");
  data.git("add", "README.md");
  data.git("commit", "-qm", "Main advances independently");
  const base = data.git("rev-parse", "HEAD");
  data.git("checkout", "--detach", data.envelope.head_sha);
  if (changeHead) {
    changeHead(data);
    data.git("add", "submissions");
    data.git("commit", "-qm", "Update the submission branch");
  }
  data.git("merge", "--no-ff", "-qm", "Refresh PR from main", base);
  data.merged.head = { sha: data.git("rev-parse", "HEAD") };
  data.merged.base.sha = base;
  data.git("checkout", "--detach", base);
  data.git("merge", "--no-ff", "--no-commit", data.merged.head.sha);
  if (changeMerge) {
    changeMerge(data);
    data.git("add", "submissions");
  }
  data.git("commit", "-qm", "Merge the refreshed PR");
  data.merged.merge_commit_sha = data.git("rev-parse", "HEAD");
  return data;
}

test("an unchanged ancestor admission survives a main refresh with its original certificate and offline provenance", async (t) => {
  const data = ancestorFixture(t);
  assert.notEqual(data.envelope.head_sha, data.merged.head.sha);
  assert.notEqual(data.merged.head.sha, data.merged.merge_commit_sha);
  const catalogue = await online(data, mockApi(data));
  const published = catalogue.records.find(
    ({ id }) => id === "candidate-proof",
  );
  assert.equal(published.source_commit, data.envelope.head_sha);
  assert.equal(
    published.first_verified_at,
    data.envelope.certificate.verified_at,
  );
  assert.equal(published.merged_at, data.merged.merged_at);
  assert.equal(
    published.solution_url,
    `https://github.com/${repository}/blob/${data.envelope.head_sha}/${data.candidatePath}/src/Candidate/Main.lean`,
  );
  const certificatePath = join(data.root, "public", published.certificate_url);
  const certificateBytes = readFileSync(certificatePath, "utf8");
  assert.deepEqual(JSON.parse(certificateBytes), data.envelope.certificate);
  const cached = JSON.parse(
    readFileSync(join(data.root, ".work/admission-records.json")),
  );
  assert.equal(cached.length, 1);
  assert.equal(cached[0].head_sha, data.envelope.head_sha);
  assert.equal(cached[0].merge_commit_sha, data.merged.merge_commit_sha);
  assert.deepEqual(cached[0].certificate, data.envelope.certificate);
  assert.deepEqual(
    await reconcileAdmissions({
      root: data.root,
      fetcher: () => assert.fail("Offline rebuild accessed the network"),
    }),
    catalogue,
  );
  assert.equal(readFileSync(certificatePath, "utf8"), certificateBytes);
});

for (const [label, directory, file] of [
  ["candidate source", "candidatePath", "src/Candidate/Main.lean"],
  ["candidate metadata", "candidatePath", "metadata.json"],
  ["dependency source", "legacyPath", "src/Candidate/Main.lean"],
  ["dependency metadata", "legacyPath", "metadata.json"],
]) {
  for (const stage of ["changeHead", "changeMerge"]) {
    test(`an ancestor receipt cannot publish changed ${label} in the ${stage === "changeHead" ? "final PR head" : "merge result"}`, async (t) => {
      const data = ancestorFixture(t, {
        [stage]: (data) => {
          const path = join(data.root, data[directory], file);
          const contents =
            file === "metadata.json"
              ? JSON.stringify({
                  ...JSON.parse(readFileSync(path)),
                  title: "Changed after verification",
                })
              : "-- Changed after verification\n";
          writeFileSync(path, contents);
        },
      });
      await assert.rejects(
        online(data, mockApi(data)),
        /Submission has no verified publication record: candidate-proof/,
      );
      assert.equal(
        existsSync(join(data.root, "catalogue/results.json")),
        false,
      );
      assert.equal(
        existsSync(join(data.root, ".work/admission-records.json")),
        false,
      );
      assert.equal(
        existsSync(join(data.root, "public/certificates/candidate-proof.json")),
        false,
      );
    });
  }
}

test("identical submission trees on an unrelated PR head cannot reuse an admission", async (t) => {
  const data = ancestorFixture(t);
  const unrelated = data.git(
    "commit-tree",
    `${data.envelope.head_sha}^{tree}`,
    "-m",
    "Unrelated identical source snapshot",
  );
  data.git("checkout", "--detach", unrelated);
  data.merged.head.sha = unrelated;
  data.merged.merge_commit_sha = unrelated;
  await assert.rejects(
    online(data, mockApi(data)),
    /Submission has no verified publication record: candidate-proof/,
  );
});

test("an ancestor receipt cannot publish a final PR head absent from the merge history", async (t) => {
  const data = ancestorFixture(t);
  data.merged.head.sha = data.git(
    "commit-tree",
    `${data.merged.head.sha}^{tree}`,
    "-p",
    data.merged.head.sha,
    "-m",
    "An identical but unmerged descendant",
  );
  await assert.rejects(
    online(data, mockApi(data)),
    /Submission has no verified publication record: candidate-proof/,
  );
});

test("an ineligible ancestor receipt does not block a valid admission for the final head", async (t) => {
  const data = ancestorFixture(t, {
    changeHead: (data) =>
      writeFileSync(
        join(data.root, data.candidatePath, "src/Candidate/Main.lean"),
        "-- A changed proof requires its own successful verification\n",
      ),
  });
  const current = structuredClone(data.envelope);
  current.head_sha = data.merged.head.sha;
  current.source_tree = data.git(
    "rev-parse",
    `${current.head_sha}:${data.candidatePath}/src`,
  );
  const report = JSON.parse(current.report_json);
  report.reviewed_pr_head = current.head_sha;
  report.verified_at = "2026-10-13T00:20:00Z";
  const bytes = Buffer.from(JSON.stringify(report));
  current.certificate = workerCertificate(
    current,
    report,
    current.certificate.report_url,
    bytes,
  );
  current.report_json = bytes.toString();
  current.admission.archived_at = "2026-10-13T00:21:00Z";
  for (const records of [
    [data.envelope, current],
    [current, data.envelope],
  ]) {
    const catalogue = await online(data, mockApi(data, { records }));
    const published = catalogue.records.find(
      ({ id }) => id === "candidate-proof",
    );
    assert.equal(published.source_commit, current.head_sha);
    assert.equal(published.first_verified_at, current.certificate.verified_at);
    assert.deepEqual(
      JSON.parse(
        readFileSync(join(data.root, "public", published.certificate_url)),
      ),
      current.certificate,
    );
    assert.deepEqual(await reconcileAdmissions({ root: data.root }), catalogue);
  }
});

test("catalogue generation uses authored metadata, exact evidence and explicit historical snapshots", (t) => {
  const data = fixture(t);
  const original = {
    ...legacyRecord(),
    id: "fixture-contribution",
    historical: true,
  };
  const revised = {
    ...original,
    historical: undefined,
    proof_revision: "fixture-revision",
    timeline_at: "2026-10-11T00:00:00Z",
  };
  delete revised.historical;
  const inputs = {
    legacy: [data.legacy, original, revised],
    admissions: [data.admission],
  };
  const before = structuredClone(inputs);
  const catalogue = generateCatalogue(inputs);
  const current = catalogue.records.find(
    (record) => record.id === "candidate-proof",
  );
  assert.equal(current.title, metadata.title);
  assert.deepEqual(current.authors, metadata.authors);
  assert.equal(current.method, metadata.description);
  assert.deepEqual(current.theta, { numerator: "4", denominator: "5" });
  assert.equal(current.source_commit, data.envelope.head_sha);
  assert.equal(
    current.first_verified_at,
    data.envelope.certificate.verified_at,
  );
  assert.equal(current.merged_at, data.merged.merged_at);
  assert.equal(
    current.references.find((reference) => reference.label === "Paper").url,
    metadata.references[0].url,
  );
  assert.equal(catalogue.historical_records[0].id, original.id);
  assert.equal(
    Object.hasOwn(catalogue.historical_records[0], "historical"),
    false,
  );
  assert.deepEqual(generateCatalogue(inputs), catalogue);
  assert.deepEqual(inputs, before);
});

test("a merged exact-head admission generates the catalogue and certificate and supports offline rebuilds", async (t) => {
  const data = fixture(t);
  const api = mockApi(data);
  const catalogue = await online(data, api);
  assert.deepEqual(
    catalogue.records.find((record) => record.id === data.legacy.id),
    data.legacy,
  );
  const record = catalogue.records.find(
    (record) => record.id === data.admission.result_id,
  );
  assert.ok(record);
  const file = join(data.root, "public", record.certificate_url);
  assert.deepEqual(JSON.parse(readFileSync(file)), data.envelope.certificate);
  assert.deepEqual(
    JSON.parse(readFileSync(join(data.root, ".work/admission-records.json"))),
    [data.admission],
  );
  const before = readFileSync(
    join(data.root, "catalogue/results.json"),
    "utf8",
  );
  await reconcileAdmissions({
    root: data.root,
    fetcher: () => assert.fail("Offline rebuild accessed the network"),
  });
  assert.equal(
    readFileSync(join(data.root, "catalogue/results.json"), "utf8"),
    before,
  );
  assert.ok(
    api.requests.every(
      (route) => !route.includes("check-runs") && !route.includes("actions/"),
    ),
    "Durable evidence does not depend on expiring checks or artifacts",
  );
});

test("a clean offline build regenerates historical verification records", async (t) => {
  const data = fixture(t);
  const path = join(data.root, "public/certificates/legacy-proof.json");
  assert.equal(existsSync(path), false);
  const catalogue = await reconcileAdmissions({ root: data.root });
  assert.deepEqual(catalogue.records, [data.legacy]);
  const receipt = JSON.parse(readFileSync(path));
  assert.deepEqual(receipt, {
    schema_version: 1,
    result_id: "legacy-proof",
    theta_exact: "7/8",
    verified_at: data.legacy.first_verified_at,
    source_repository: repository,
    source_commit: data.legacy.source_commit,
    kernels: ["Lean default", "nanoda", "con-ron"],
    report_url: `https://github.com/${repository}/actions/runs/100`,
    report_sha256: "f".repeat(64),
  });
  rmSync(join(data.root, "public"), { recursive: true });
  await reconcileAdmissions({ root: data.root });
  assert.deepEqual(JSON.parse(readFileSync(path)), receipt);
});

test("date-first folder migration preserves historical catalogue entries, certificates and admission provenance", async (t) => {
  const data = fixture(t);
  const before = await online(data, mockApi(data));
  const certificatePath = join(
    data.root,
    "public/certificates/candidate-proof.json",
  );
  const certificateBytes = readFileSync(certificatePath, "utf8");
  const cachePath = join(data.root, ".work/admission-records.json");
  const cacheBytes = readFileSync(cachePath, "utf8");
  data.git("add", "submissions");
  for (const [path, dated] of [
    [data.candidatePath, "submissions/2026-10-12-candidate-proof"],
    [data.legacyPath, "submissions/2026-10-10-legacy-proof"],
  ])
    data.git("mv", path, dated);
  data.git(
    "-c",
    "user.name=Test",
    "-c",
    "user.email=test@example.com",
    "commit",
    "-qm",
    "Date-first folder migration",
  );
  const after = await online(data, mockApi(data));
  assert.deepEqual(after, before);
  assert.equal(readFileSync(certificatePath, "utf8"), certificateBytes);
  assert.equal(readFileSync(cachePath, "utf8"), cacheBytes);
  assert.deepEqual(await reconcileAdmissions({ root: data.root }), before);
  const candidate = after.records.find(({ id }) => id === "candidate-proof");
  assert.equal(candidate.source_commit, data.envelope.head_sha);
  assert.equal(
    candidate.solution_url,
    `https://github.com/${repository}/blob/${data.envelope.head_sha}/submissions/candidate-proof/src/Candidate/Main.lean`,
  );
});

test("dated admissions authenticate dependency paths and trees at their immutable merge commit", async (t) => {
  const data = fixture(t, { dated: true, dependencies: true });
  const catalogue = await online(data, mockApi(data));
  const published = catalogue.records.find(
    ({ id }) => id === "candidate-proof",
  );
  assert.equal(published.id, data.envelope.result_id);
  assert.equal(
    published.solution_url,
    `https://github.com/${repository}/blob/${data.envelope.head_sha}/${data.candidatePath}/src/Candidate/Main.lean`,
  );
  assert.equal(data.envelope.source_path, `${data.candidatePath}/src`);
  assert.equal(
    data.envelope.dependency_trees["legacy-proof"],
    data.git("rev-parse", `${data.merged.merge_commit_sha}:${data.legacyPath}`),
  );
  writeFileSync(
    join(data.root, data.legacyPath, "src/Candidate/Main.lean"),
    "-- Later dependency maintenance\n",
  );
  data.git("add", "submissions");
  data.git(
    "-c",
    "user.name=Test",
    "-c",
    "user.email=test@example.com",
    "commit",
    "-qm",
    "Maintain dependency after admission",
  );
  assert.deepEqual(await online(data, mockApi(data)), catalogue);
  assert.deepEqual(await reconcileAdmissions({ root: data.root }), catalogue);
  const forged = structuredClone(data.envelope);
  forged.dependency_trees["legacy-proof"] = data.git(
    "rev-parse",
    `HEAD:${data.legacyPath}`,
  );
  assert.notEqual(
    forged.dependency_trees["legacy-proof"],
    data.envelope.dependency_trees["legacy-proof"],
  );
  await assert.rejects(
    online(data, mockApi(data, { records: [forged] })),
    /Merged dependency differs from verified admission: legacy-proof/,
  );
  assert.deepEqual(
    JSON.parse(readFileSync(join(data.root, ".work/admission-records.json"))),
    [data.admission],
  );
});

test("missing historical report provenance fails before publishing generated files", async (t) => {
  const data = fixture(t);
  writeFileSync(
    join(data.root, "submissions/legacy-proof/metadata.json"),
    JSON.stringify(data.legacy),
  );
  await assert.rejects(
    reconcileAdmissions({ root: data.root }),
    /Invalid verification record/,
  );
  assert.equal(existsSync(join(data.root, "public/certificates")), false);
  assert.equal(existsSync(join(data.root, "catalogue/results.json")), false);
});

test("historical certificate paths are validated before writing output", async (t) => {
  const data = fixture(t);
  const path = join(data.root, "submissions/legacy-proof/metadata.json");
  const metadata = JSON.parse(readFileSync(path));
  metadata.certificate_url = "../outside.json";
  writeFileSync(path, JSON.stringify(metadata));
  await assert.rejects(
    reconcileAdmissions({ root: data.root }),
    /Invalid verification record path: legacy-proof/,
  );
  assert.equal(existsSync(join(data.root, "outside.json")), false);
  assert.equal(existsSync(join(data.root, "public/certificates")), false);
});

test("historical and current proof revisions both regenerate their receipts", async (t) => {
  const data = fixture(t);
  const oldPath = join(data.root, "submissions/legacy-proof/metadata.json");
  const original = JSON.parse(readFileSync(oldPath));
  writeFileSync(oldPath, JSON.stringify({ ...original, historical: true }));
  const revised = {
    ...original,
    proof_revision: "legacy-revised",
    timeline_at: "2026-10-11T00:00:00Z",
    certificate_url: "certificates/legacy-revised.json",
  };
  const dir = join(data.root, "submissions/legacy-revised");
  mkdirSync(join(dir, "src/Candidate"), { recursive: true });
  writeFileSync(join(dir, "metadata.json"), JSON.stringify(revised));
  writeFileSync(join(dir, "src/Candidate/Main.lean"), "-- fixture source\n");
  const catalogue = await reconcileAdmissions({ root: data.root });
  assert.equal(catalogue.records.length, 1);
  assert.equal(catalogue.historical_records.length, 1);
  for (const id of ["legacy-proof", "legacy-revised"])
    assert.equal(
      JSON.parse(
        readFileSync(join(data.root, `public/certificates/${id}.json`)),
      ).result_id,
      id,
    );
});

for (const [label, change] of [
  [
    "unmerged PR",
    (pr) => {
      pr.merged = false;
      pr.state = "open";
    },
  ],
  [
    "stale PR head",
    (pr) => {
      pr.head.sha = hex("f");
    },
  ],
  [
    "different target branch",
    (pr) => {
      pr.base.ref = "other";
    },
  ],
  [
    "different base repository",
    (pr) => {
      pr.base.repo.full_name = "other/repository";
    },
  ],
])
  test(`does not publish checked-out source from an ${label}`, async (t) => {
    const data = fixture(t);
    change(data.merged);
    await assert.rejects(
      online(data, mockApi(data)),
      /no verified publication record/,
    );
    assert.equal(
      existsSync(join(data.root, "public/certificates/candidate-proof.json")),
      false,
    );
  });

test("later source maintenance preserves the original admitted proof and pinned evidence", async (t) => {
  const data = fixture(t);
  writeFileSync(
    join(data.root, "submissions/candidate-proof/src/Candidate/Main.lean"),
    "-- changed source\n",
  );
  data.git("add", "submissions");
  data.git(
    "-c",
    "user.name=Test",
    "-c",
    "user.email=test@example.com",
    "commit",
    "-qm",
    "Different source",
  );
  const catalogue = await online(data, mockApi(data));
  assert.equal(
    catalogue.records.find((record) => record.id === data.admission.result_id)
      .source_commit,
    data.envelope.head_sha,
  );
  const offline = await reconcileAdmissions({ root: data.root });
  assert.deepEqual(offline, catalogue);
});

test("the immutable merge source must match the independently verified source tree", async (t) => {
  const data = fixture(t);
  data.envelope.source_tree = hex("f");
  await assert.rejects(online(data, mockApi(data)), /Merged source differs/);
  assert.equal(existsSync(join(data.root, "catalogue/results.json")), false);
  assert.equal(
    existsSync(join(data.root, ".work/admission-records.json")),
    false,
  );
});

test("conflicting certificates fail before changing generated catalogue or cache", async (t) => {
  const data = fixture(t);
  mkdirSync(join(data.root, "public/certificates"), { recursive: true });
  const path = join(data.root, "public/certificates/candidate-proof.json");
  const conflicting = {
    ...data.envelope.certificate,
    report_sha256: "f".repeat(64),
  };
  writeFileSync(path, JSON.stringify(conflicting));
  await assert.rejects(online(data, mockApi(data)), /certificate conflicts/);
  assert.deepEqual(JSON.parse(readFileSync(path)), conflicting);
  assert.equal(existsSync(join(data.root, "catalogue/results.json")), false);
});

test("reviewed metadata is preserved and conflicting reuse of a result ID is rejected", (t) => {
  const data = fixture(t);
  const existing = {
    ...data.legacy,
    id: data.admission.result_id,
    theta: { numerator: "4", denominator: "5" },
  };
  assert.deepEqual(
    generateCatalogue({ legacy: [existing], admissions: [data.admission] })
      .records,
    [existing],
  );
  existing.theta = { numerator: "3", denominator: "4" };
  assert.throws(
    () =>
      generateCatalogue({ legacy: [existing], admissions: [data.admission] }),
    /Conflicting exact bound/,
  );
  const changed = {
    ...data.admission,
    number: 27,
    pr: { ...data.admission.pr, number: 27 },
    source_tree: hex("f"),
  };
  assert.throws(
    () =>
      generateCatalogue({
        legacy: [data.legacy],
        admissions: [data.admission, changed],
      }),
    /Conflicting admitted source/,
  );
});

test("missing archive branch permits legacy-only builds without artifact fallback", async (t) => {
  const data = fixture(t);
  data.git("rm", "-r", "submissions");
  data.git(
    "-c",
    "user.name=Test",
    "-c",
    "user.email=test@example.com",
    "commit",
    "-qm",
    "Legacy-only checkout",
  );
  const api = mockApi(data, {
    overrides: { "git/ref/heads/admission-records": null },
  });
  assert.deepEqual((await online(data, api)).records, [data.legacy]);
  assert.deepEqual(api.requests, ["git/ref/heads/admission-records"]);
});

test("missing admission evidence cannot silently omit a merged proof from the website", async (t) => {
  const data = fixture(t);
  const api = mockApi(data, {
    overrides: { "git/ref/heads/admission-records": null },
  });
  await assert.rejects(
    online(data, api),
    /Submission has no verified publication record: candidate-proof/,
  );
  assert.equal(existsSync(join(data.root, "catalogue/results.json")), false);
  const offline = await reconcileAdmissions({ root: data.root });
  assert.deepEqual(
    offline.records,
    [data.legacy],
    "Offline PR builds need not admit their candidate source",
  );
});

test("older main checkouts ignore a later merged proof whose source is not yet present", async (t) => {
  const data = fixture(t);
  data.git("checkout", "--detach", data.earlier);
  const catalogue = await online(data, mockApi(data));
  assert.deepEqual(catalogue.records, [data.legacy]);
  assert.deepEqual(
    JSON.parse(readFileSync(join(data.root, ".work/admission-records.json"))),
    [],
  );
});

test("truncated archive trees and path/identity mismatches fail closed", async (t) => {
  const data = fixture(t);
  const treeRoute = `git/trees/${hex("e")}?recursive=1`;
  await assert.rejects(
    online(
      data,
      mockApi(data, {
        overrides: { [treeRoute]: { truncated: true, tree: [] } },
      }),
    ),
    /Incomplete admission archive/,
  );
  const wrongPath = {
    truncated: false,
    tree: [
      {
        path: admissionPath(data.envelope).replace(
          "records/26/",
          "records/27/",
        ),
        mode: "100644",
        type: "blob",
        sha: hex("1"),
      },
    ],
  };
  await assert.rejects(
    online(data, mockApi(data, { overrides: { [treeRoute]: wrongPath } })),
    /path differs from record/,
  );
});

test("changing cached metadata cannot detach it from the admitted PR body", async (t) => {
  const data = fixture(t);
  await online(data, mockApi(data));
  const changed = structuredClone(data.admission);
  changed.metadata.title = "Unreviewed replacement";
  writeFileSync(
    join(data.root, ".work/admission-records.json"),
    JSON.stringify([changed]),
  );
  await assert.rejects(
    reconcileAdmissions({ root: data.root }),
    /metadata|Metadata/,
  );
});

test("deployment uses colocated metadata and the latest pre-merge verification", async (t) => {
  const data = fixture(t);
  const revision = (attempt, archivedAt, title) => {
    const record = structuredClone(data.envelope);
    record.metadata.title = title;
    record.metadata_sha256 = sha256(canonical(record.metadata));
    record.pr.body = record.pr.body.replace(
      JSON.stringify(metadata),
      JSON.stringify(record.metadata),
    );
    record.admission.run_attempt = String(attempt);
    record.admission.archived_at = archivedAt;
    record.certificate.report_url = record.certificate.report_url.replace(
      "/attempts/1",
      `/attempts/${attempt}`,
    );
    return record;
  };
  const latest = revision(
    2,
    "2026-10-13T00:30:00Z",
    "Corrected author-provided title",
  );
  const afterMerge = revision(
    3,
    "2026-10-13T02:00:00Z",
    "A later edit must not change the publication",
  );
  data.merged.body =
    "The current editable PR description is not publication evidence.";
  const catalogue = await online(
    data,
    mockApi(data, { records: [afterMerge, data.envelope, latest] }),
  );
  const published = catalogue.records.find(
    (record) => record.id === latest.result_id,
  );
  assert.equal(published.title, metadata.title);
  assert.deepEqual(
    JSON.parse(
      readFileSync(join(data.root, "public", published.certificate_url)),
    ),
    data.envelope.certificate,
  );
  assert.deepEqual(
    JSON.parse(readFileSync(join(data.root, ".work/admission-records.json"))),
    [
      data.admission,
      {
        ...latest,
        merged_at: data.merged.merged_at,
        merge_commit_sha: data.merged.merge_commit_sha,
      },
    ],
  );
});

function rerun(
  original,
  {
    attempt = 2,
    verifiedAt = "2026-10-13T00:20:00Z",
    archivedAt = "2026-10-13T00:21:00Z",
  } = {},
) {
  const value = structuredClone(original);
  value.admission.run_attempt = String(attempt);
  value.admission.archived_at = archivedAt;
  const report = JSON.parse(value.report_json);
  report.verified_at = verifiedAt;
  const bytes = Buffer.from(JSON.stringify(report));
  value.certificate = workerCertificate(
    value,
    report,
    `https://github.com/${repository}/actions/runs/${value.admission.run_id}/attempts/${attempt}`,
    bytes,
  );
  value.report_json = bytes.toString();
  return value;
}

test("reruns retain the first success, latest metadata and every receipt through online and offline rebuilds", async (t) => {
  const data = fixture(t);
  const later = rerun(data.envelope);
  later.metadata.title = "Corrected attribution";
  later.metadata_sha256 = sha256(canonical(later.metadata));
  writeFileSync(
    join(data.root, "submissions/candidate-proof/metadata.json"),
    JSON.stringify(later.metadata),
  );
  later.pr.body = later.pr.body.replace(
    JSON.stringify(metadata),
    JSON.stringify(later.metadata),
  );
  // An existing deployment selected the rerun; migration may replace only this
  // exact authenticated certificate, not a fabricated or unrelated receipt.
  const path = join(data.root, "public/certificates/candidate-proof.json");
  mkdirSync(join(data.root, "public/certificates"), { recursive: true });
  writeFileSync(path, JSON.stringify(later.certificate));
  const catalogue = await online(
    data,
    mockApi(data, { records: [later, data.envelope] }),
  );
  const record = catalogue.records.find(
    (r) => r.id === data.envelope.result_id,
  );
  assert.equal(record.first_verified_at, data.envelope.certificate.verified_at);
  assert.equal(record.timeline_at, data.envelope.pr.created_at);
  assert.equal(record.title, later.metadata.title);
  assert.deepEqual(JSON.parse(readFileSync(path)), data.envelope.certificate);
  assert.equal(
    JSON.parse(readFileSync(join(data.root, ".work/admission-records.json")))
      .length,
    2,
  );
  assert.deepEqual(await reconcileAdmissions({ root: data.root }), catalogue);
  // Input order cannot determine the first verification or metadata selection.
  assert.deepEqual(
    await online(data, mockApi(data, { records: [data.envelope, later] })),
    catalogue,
  );
});

test("the earliest verification is selected by success time rather than archive order", (t) => {
  const data = fixture(t);
  const earlierSuccess = rerun(data.admission, {
    verifiedAt: "2026-10-12T23:00:00Z",
  });
  const result = generateCatalogue({
    legacy: [data.legacy],
    admissions: [data.admission, earlierSuccess],
  });
  assert.equal(
    result.records.at(-1).first_verified_at,
    earlierSuccess.certificate.verified_at,
  );
});

test("a conflicting source tree cannot lend its earlier verification date to a rerun", (t) => {
  const data = fixture(t);
  const different = rerun(data.admission);
  different.source_tree = hex("f");
  assert.throws(
    () =>
      generateCatalogue({
        legacy: [data.legacy],
        admissions: [data.admission, different],
      }),
    /Conflicting admitted proof identity/,
  );
});

test("a stale source head cannot lend its first verification date to the merged revision", async (t) => {
  const data = fixture(t);
  const stale = structuredClone(data.envelope);
  stale.head_sha = hex("f");
  const report = JSON.parse(stale.report_json);
  report.reviewed_pr_head = stale.head_sha;
  report.verified_at = "2026-10-12T12:00:00Z";
  const bytes = Buffer.from(JSON.stringify(report));
  stale.certificate = workerCertificate(
    stale,
    report,
    stale.certificate.report_url,
    bytes,
  );
  stale.report_json = bytes.toString();
  const result = await online(
    data,
    mockApi(data, { records: [stale, data.envelope] }),
  );
  assert.equal(
    result.records.at(-1).first_verified_at,
    data.envelope.certificate.verified_at,
  );
});

test("submission chronology preserves an intermediate record even when the stronger proof verifies first", (t) => {
  const data = fixture(t);
  const first = data.admission;
  const second = structuredClone(first);
  second.number = second.pr.number = 27;
  second.result_id = "stronger-proof";
  second.theta_exact = "3/4";
  second.source_path = "submissions/stronger-proof/src";
  second.pr.created_at = "2026-10-12T01:00:00Z";
  second.pr.body = second.pr.body
    .replaceAll("candidate-proof", "stronger-proof")
    .replace("4/5", "3/4")
    .replace("QRH-Decimal: 0.8", "QRH-Decimal: 0.75");
  const report = JSON.parse(second.report_json);
  report.result_id = second.result_id;
  report.theta_exact = second.theta_exact;
  report.verified_at = "2026-10-12T23:59:33Z";
  const bytes = Buffer.from(JSON.stringify(report));
  second.certificate = workerCertificate(
    second,
    report,
    second.certificate.report_url,
    bytes,
  );
  second.report_json = bytes.toString();
  const result = generateCatalogue({
    legacy: [data.legacy],
    admissions: [second, first],
  });
  assert.deepEqual(
    recordHistory(timelineRecords(result.records)).map((r) => [
      r.id,
      r.is_record,
    ]),
    [
      [data.legacy.id, true],
      [first.result_id, true],
      [second.result_id, true],
    ],
  );
  assert.equal(
    result.records[1].first_verified_at,
    first.certificate.verified_at,
  );
  assert.equal(
    result.records[2].first_verified_at,
    second.certificate.verified_at,
  );
});

test("GitHub's second-resolution merge date does not exclude an archive in the same second", async (t) => {
  const data = fixture(t);
  data.envelope.admission.archived_at = "2026-10-13T01:00:00.999Z";
  const catalogue = await online(data, mockApi(data));
  assert.ok(
    catalogue.records.some((record) => record.id === data.envelope.result_id),
  );
});
