import test from "node:test";
import assert from "node:assert/strict";
import {
  classifyChanges,
  evaluatePR,
  parseDeclaration,
} from "../verifier/pr-admission.mjs";

const repository = "GTimG/QuasiRiemannTracker";
const defaultBranch = "main";
const head = "a".repeat(40);
const root = "/unused/trusted-checkout";
const bound = "4374433/5000000";
const resultId = "candidate-20261011";
const maintenance = "QRH-Type: maintenance";
const newBound = [
  "QRH-Type: new-bound",
  `QRH-Result: ${resultId}`,
  `QRH-Bound: ${bound}`,
].join("\n");
const file = (filename, extra = {}) => ({
  filename,
  status: "added",
  ...extra,
});

function options(body = maintenance, files = [file("README.md")]) {
  return {
    repository,
    defaultBranch,
    root,
    files,
    pr: {
      number: 15,
      state: "open",
      draft: false,
      body,
      changed_files: files.length,
      base: { ref: defaultBranch, repo: { full_name: repository } },
      head: { sha: head },
    },
    validateEvidence: () => {
      throw new Error("Unexpected evidence validation");
    },
  };
}

// Accept either a synchronous or asynchronous implementation of the gate.
const run = (input) => Promise.resolve().then(() => evaluatePR(input));

test("maintenance has a single unambiguous declaration", () => {
  assert.deepEqual(parseDeclaration(maintenance), { type: "maintenance" });
});

test("a new-bound declaration preserves the exact claimed value", () => {
  assert.deepEqual(parseDeclaration(`A proposed bound.\n\n${newBound}\n`), {
    type: "new-bound",
    result_id: resultId,
    theta_exact: bound,
  });
});

for (const [description, body] of [
  ["a missing declaration", "This adds a proof of a better bound."],
  ["an empty body", ""],
  ["a null body", null],
  ["an inline declaration", "Please review QRH-Type: maintenance"],
  ["a missing colon", "QRH-Type maintenance"],
  ["a misspelled type", "QRH-Type: new_bound"],
  ["a type with trailing commentary", "QRH-Type: maintenance (docs only)"],
  ["a duplicate type", `${maintenance}\n${maintenance}`],
  ["contradictory types", `${maintenance}\n${newBound}`],
  ["an unknown field", `${maintenance}\nQRH-Override: true`],
  ["a bound on maintenance", `${maintenance}\nQRH-Bound: ${bound}`],
  ["a result on maintenance", `${maintenance}\nQRH-Result: ${resultId}`],
  ["a missing result", `QRH-Type: new-bound\nQRH-Bound: ${bound}`],
  ["a missing bound", `QRH-Type: new-bound\nQRH-Result: ${resultId}`],
  ["a duplicate result", `${newBound}\nQRH-Result: ${resultId}`],
  ["a duplicate bound", `${newBound}\nQRH-Bound: ${bound}`],
  ["an empty result", newBound.replace(resultId, "")],
  ["an uppercase result", newBound.replace(resultId, "Candidate-20261011")],
  ["a short result", newBound.replace(resultId, "ab")],
  ["a path as result", newBound.replace(resultId, "../candidate")],
  ["an empty bound", newBound.replace(bound, "")],
  ["an oversized bound", newBound.replace(bound, "1".repeat(257))],
]) {
  test(`declaration rejects ${description}`, () => {
    assert.throws(() => parseDeclaration(body));
  });
}

for (const filename of [
  "proofs/candidate/Main.lean",
  "public/proofs/candidate/report.json",
  "submissions/candidate.json",
  "catalogue/records/candidate.json",
  "registry/records/candidate.json",
  "public/catalogue.json",
  "public/registry.json",
  "Candidate/Main.lean",
  "Main.lean",
]) {
  test(`classifies ${filename} as proof-bearing`, () => {
    assert.equal(classifyChanges([file(filename)]), true);
  });
}

test("ordinary maintenance paths and trusted Lean fixtures are not submissions", () => {
  assert.equal(
    classifyChanges([
      file("README.md"),
      file("src/App.tsx"),
      file("docs/submission.md"),
      file(".github/workflows/ci.yml"),
      file("core/Challenge.lean"),
      file("verifier/fixtures/Example.lean"),
      file("tests/fixtures/Example.lean"),
    ]),
    false,
  );
});

test("renaming a proof to a maintenance path remains proof-bearing", () => {
  assert.equal(
    classifyChanges([
      file("docs/old-proof.txt", {
        status: "renamed",
        previous_filename: "proofs/candidate/Main.lean",
      }),
    ]),
    true,
  );
});

test("a declared maintenance PR can pass without bound evidence", async () => {
  const summary = await run(options());
  assert.equal(typeof summary, "string");
  assert.ok(summary.length > 0);
});

test("PR #15's proof-only change cannot pass without a declaration", async () => {
  const input = options("Adds the Lean proof.", [file("proofs/solution.lean")]);
  input.pr.number = 15;
  await assert.rejects(run(input));
});

test("a proof submission cannot bypass admission by declaring maintenance", async () => {
  await assert.rejects(
    run(options(maintenance, [file("proofs/candidate/Main.lean")])),
  );
});

test("a proof renamed out of the protected directories cannot declare maintenance", async () => {
  await assert.rejects(
    run(
      options(maintenance, [
        file("docs/old-proof.txt", {
          status: "renamed",
          previous_filename: "public/proofs/candidate/report.json",
        }),
      ]),
    ),
  );
});

test("a new-bound declaration requires a proof-bearing change", async () => {
  await assert.rejects(run(options(newBound)));
});

test("new-bound admission binds evidence to the repository, PR, current head, result and value", async () => {
  const input = options(newBound, [file("proofs/candidate/Main.lean")]);
  const calls = [];
  input.validateEvidence = (...args) => {
    calls.push(args);
    return { result_id: resultId, theta_exact: bound };
  };
  const summary = await run(input);
  assert.equal(typeof summary, "string");
  assert.ok(summary.length > 0);
  assert.deepEqual(calls, [
    [
      root,
      {
        repository,
        number: 15,
        head_sha: head,
        result_id: resultId,
        theta_exact: bound,
      },
    ],
  ]);
});

test("a failed evidence check fails the PR instead of passing on existing repository checks", async () => {
  const input = options(newBound, [file("proofs/candidate/Main.lean")]);
  input.validateEvidence = () => {
    throw new Error("No trusted admission receipt for this PR head");
  };
  await assert.rejects(run(input), /No trusted admission receipt/);
});

test("pushing a new head cannot reuse a receipt for the old commit", async () => {
  const input = options(newBound, [file("proofs/candidate/Main.lean")]);
  input.pr.head.sha = "b".repeat(40);
  input.validateEvidence = (_root, subject) => {
    assert.equal(subject.head_sha, input.pr.head.sha);
    if (subject.head_sha !== head)
      throw new Error("Receipt head does not match");
  };
  await assert.rejects(run(input), /Receipt head does not match/);
});

for (const filename of [
  ".github/workflows/ci.yml",
  "core/trust-root.json",
  "verifier/pr-admission.mjs",
  "tests/pr-admission.test.mjs",
  "README.md",
]) {
  test(`a bound cannot also modify ${filename}`, async () => {
    let evidenceCalls = 0;
    const input = options(newBound, [
      file("proofs/candidate/Main.lean"),
      file(filename),
    ]);
    input.validateEvidence = () => {
      evidenceCalls++;
    };
    await assert.rejects(run(input));
    assert.equal(evidenceCalls, 0);
  });
}

for (const [description, mutate] of [
  ["closed PR", (input) => (input.pr.state = "closed")],
  ["draft PR", (input) => (input.pr.draft = true)],
  ["different base branch", (input) => (input.pr.base.ref = "other")],
  [
    "different base repository",
    (input) => (input.pr.base.repo.full_name = "Elsewhere/Tracker"),
  ],
  ["missing head", (input) => delete input.pr.head],
  ["short head SHA", (input) => (input.pr.head.sha = "abcd")],
  ["nonhex head SHA", (input) => (input.pr.head.sha = "z".repeat(40))],
  ["truncated file list", (input) => (input.pr.changed_files = 2)],
  ["inconsistent file count", (input) => (input.pr.changed_files = 0)],
]) {
  test(`admission rejects a ${description}`, async () => {
    const input = options();
    mutate(input);
    await assert.rejects(run(input));
  });
}
