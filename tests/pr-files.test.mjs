import test from "node:test";
import assert from "node:assert/strict";
import { execFileSync } from "node:child_process";
import {
  mkdtempSync,
  mkdirSync,
  writeFileSync,
  renameSync,
  rmSync,
} from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { gitChangedFiles, prFiles } from "../verifier/pr-files.mjs";
import { evaluatePR } from "../verifier/pr-admission.mjs";

test("a large Git diff includes maintenance beyond the API limit and both renamed paths", async (t) => {
  const dir = mkdtempSync(join(tmpdir(), "qrh-large-diff-test-"));
  t.after(() => rmSync(dir, { recursive: true, force: true }));
  const git = (...args) =>
    execFileSync("git", args, { cwd: dir, encoding: "utf8" }).trim();
  git("init", "--quiet");
  git("config", "user.name", "Test");
  git("config", "user.email", "test@example.com");
  mkdirSync(join(dir, "proofs"));
  writeFileSync(
    join(dir, "proofs/original.lean"),
    "theorem original : True := trivial\n",
  );
  git("add", ".");
  git("commit", "--quiet", "-m", "base");
  const base = git("rev-parse", "HEAD");
  for (let i = 0; i < 3001; i++)
    writeFileSync(join(dir, `proofs/${i}.lean`), `-- ${i}\n`);
  mkdirSync(join(dir, "zz-maintenance"));
  renameSync(
    join(dir, "proofs/original.lean"),
    join(dir, "zz-maintenance/renamed\nfile.md"),
  );
  git("add", ".");
  git("commit", "--quiet", "-m", "large contribution");
  const head = git("rev-parse", "HEAD");
  const repository = "Owner/Repo";
  const pr = {
    number: 8,
    state: "open",
    draft: false,
    body: "QRH-Result: sample-bound",
    changed_files: 3002,
    head: { sha: head },
    base: { sha: base, ref: "main", repo: { full_name: repository } },
  };
  const files = await prFiles(pr, repository, {
    apiFiles: () => {
      throw Error("Large diff must use Git");
    },
    gitFiles: () => gitChangedFiles(dir, base, head),
  });
  assert.equal(files.length, 3002);
  assert.deepEqual(
    files.find((f) => f.status === "renamed"),
    {
      filename: "zz-maintenance/renamed\nfile.md",
      previous_filename: "proofs/original.lean",
      status: "renamed",
    },
  );
  await assert.rejects(
    evaluatePR({ pr, files, repository, defaultBranch: "main" }),
    {
      message: "Submit QRH results and maintenance changes in separate PRs",
    },
  );
  await assert.rejects(
    prFiles({ ...pr, changed_files: 3003 }, repository, {
      gitFiles: () => files,
    }),
    {
      message: "Git diff disagrees with PR changed-file count",
    },
  );
});

test("ordinary diffs keep API pagination and its completeness check", async () => {
  const files = [{ filename: "README.md", status: "modified" }];
  assert.equal(
    await prFiles({ changed_files: 1 }, "Owner/Repo", {
      apiFiles: () => files,
      gitFiles: () => {
        throw Error("Unexpected Git fallback");
      },
    }),
    files,
  );
});
