# Submission process: upstream changes since 1dee293b

Read-only research. Nothing was committed, pushed, posted or edited in the repository.

- Reference: `upstream/main` = 659086ca (merge of PR #85). 54 upstream commits after the divergence point 1dee293b (2026-10-23).
- Citations are `path:line` in `upstream/main` unless marked "ours" (our working tree).
- Scratch material in `$SCRATCH/analysis/`: `upstream/` (a `git archive` extract), `probe.mjs`, `probe2.mjs`, `top.py`, `closure.py`, `pkgclosure.py`, `policy.mjs`.
- Check: `node --test` on the four `tests/submission-*.test.mjs` files in the extract passes 29/29.

Main changes since 1dee293b:
1. Dated folders with a stable-ID map (4ac28350).
2. "Author ·" title prefixes removed from legacy titles (aef08ac2).
3. Admission moved to self-hosted proof runners with a 12-hour replay budget (10425a8c, 8d979e29, c1fa265f, d6f04ea7, 6070a30c, 65a8a3a4).
4. Receipt reuse for maintainer-registered PRs (405cbb4e and registration commits).
5. Stricter dependency and publication checks.

---

## 1. Submission layout rules

### 1.1 Folder name (`verifier/submission-paths.mjs`)

- Required pattern (`:10`): `const datedPattern = /^(\d{4}-\d{2}-\d{2})-([a-z][a-z0-9-]{2,63})$/;`
- The date must be a real calendar date (`:12-14`) and may appear only once. `dateToken` (`:11`) is `/(?:^|-)(\d{4})-?(\d{2})-?(\d{2})(?=-|$)/g`, so a slug containing a valid `YYYY-MM-DD` or `YYYYMMDD` token is rejected. Message (`:26`): `use YYYY-MM-DD-<result-id> with the date only once`.
- The date must equal the UTC date of the PR's `created_at` (`:28-35`, message `Submission directory must start with the PR submission date ${date}`). Enforced for result PRs at `verifier/pr-admission.mjs:164-166`. For renames in maintenance PRs it uses the original date (`verifier/pr-maintenance.mjs:142-152`).
- Only directories may sit directly under `submissions/` (`scripts/reconcile-admissions.mjs:333-335`).
- Result ID: the slug without the date (`:53`). Legacy folders keep their old ID from `verifier/submission-directories.json` (38 entries; 35 are folders on main, 3 reserve IDs for folders absent from main). Two folders with one ID fail with `Duplicate submission directories` (`:61`).

Probed: `2026-10-29-arvi-mixed-step` is valid with ID `arvi-mixed-step`. Rejected: `…-arvi-mixed-step-20261026` (date token), `…-Arvi-mixed` and `…-arvi_mixed` (charset), `…-ab` (too short), `…-1arvi` (leading digit). A `2026-10-29` folder for a PR created `2026-10-28T23:59Z` is rejected.

### 1.2 Required files and allowed contents (`verifier/manifest.mjs`)

- Required: `metadata.json` and `src/Candidate/Main.lean` (`:79-82`; `verifier/pr-maintenance.mjs:136-141`).
- Only `metadata.json` and `.lean` files are allowed, under `src/Candidate/` or `src/Submissions/`:
  - directories (`:50`): `^src\/(?:Candidate|Submissions)(?:\/[A-Za-z_][A-Za-z0-9_]*)*$`
  - files (`:60`): `^src\/(?:Candidate|Submissions)\/(?:[A-Za-z_][A-Za-z0-9_]*\/)*[A-Za-z_][A-Za-z0-9_]*\.lean$`
  - So no README or other files in the folder, and no hyphens in Lean path segments.
- Symlinks are rejected (`:36`, `:45-46`). Size limits (`:68-73`): 2 MiB per `.lean`, 64 MiB and at most 8191 files per folder. `metadata.json` is at most 64 KiB (`:83-84`).

### 1.3 Lean names

- Entry point: `Candidate.bound` in `Candidate.Main` (`manifest.mjs:19`; `verifier/upstream-challenge.lean:8-10` gives the binders).
- Own modules must be `Candidate.*` or `Submissions.<result_id with - replaced by _>.*` (`verifier/submission-dependencies.mjs:3-4`, `:43-44`: `Module ${name} must belong to ${own}`).
- Importing another submission requires a declared dependency (`:72-77`: `Undeclared dependency: ${owner} imports ${target.owner}`).
- `import OAI…` is refused (`:62-63`). Use `Submissions.openai_baseline.OAI…` (README:120-129).
- Module-name regex in the replay: `verifier/standard/replay.py:138`.

### 1.4 metadata.json (`verifier/submission-metadata.mjs`)

- Allowed keys only (`:15-23`): `title`, `authors`, `description`, `license`, `builds_on`, `references`, `dependencies`. Any other key fails (probed with `theta`).
- `title` at most 240 (`:29`). `description` at most 10000 (`:30`). 1 to 100 authors with `name` and optional https `url` (`:31-42`). `license` at most 1000 (`:43`).
- `builds_on`: at most 100 unique IDs matching `^[a-z][a-z0-9-]{2,63}$` (`:44-48`). `references`: at most 100, https URLs only (`:49-62`).
- `dependencies` (`verifier/submission-dependencies.mjs:9-15`): at most 256, unique, same ID regex. A dated folder name fails the regex.
- No date fields. Dates come from the PR.
- Titles: no code rule. Commit aef08ac2 removed `Author · ` prefixes from 9 legacy titles. The validator accepts `ArviFoxy · x` (probed), so this is convention only.

### 1.5 What the four test files enforce (all pass)

- `tests/submission-paths.test.mjs`
  - 12-28: IDs from dated folders.
  - 30-69: calendar dates, and rejected names such as `2026-10-27-example_proof` and `2026-10-27-example-proof-20261027`.
  - 71-93: UTC PR date, including offsets (`2026-10-28T00:30:00+02:00` maps to folder `2026-10-27`).
  - 95-113: legacy IDs preserved. `2026-10-27-openai-baseline` is rejected.
  - 115-125: duplicate IDs.
  - 127-152: source-path binding.
- `tests/submission-layout.test.mjs`
  - 39-62: missing files and symlinks.
  - 63-87: every folder is dated and complete. Seven named legacy IDs must exist.
  - 103-120: metadata edits change the inventory hash.
- `tests/submission-metadata.test.mjs`
  - 38-57: publication metadata cannot carry `status` or `theta_exact`, empty title or authors, `javascript:` or credentialed URLs, `../` in `builds_on`, or duplicate `builds_on`.
  - 119-139: dated paths keep result identity. Duplicates rejected.
  - 140-180: dated dependencies resolve by stable ID.
  - 193-216: missing dependency and cycles.
- `tests/submission-dependencies.test.mjs`
  - 53-96: undeclared and missing imports, cycles, ownership, OAI.
  - 97-107: dependency ID validation.
  - 108-120: every folder resolves its import closure.

---

## 2. Admission requirements

### 2.1 Documents

- PR template `.github/PULL_REQUEST_TEMPLATE.md:21-31`: the author must confirm the directory rule, and that the proof and its dependencies "must build and pass Comparator, Lean, NanoDa, and con-ron within **12 hours** on one **6-vCPU x86-64 Linux worker with 24 GiB total RAM and an 80 GiB disk**. Queue time and checking-environment setup are separate; lower sandbox memory limits and individual phase deadlines also apply." Nothing in the verifier checks these checkboxes.
- Commit d6f04ea7 added a full README section. It stated 30 minutes per source module, 10 minutes per export, 3 hours for the combined final checking, and "Caches may accelerate a replay but do not increase its resource limits." Commit 6070a30c removed it from the README and kept the requirements in the template. The code matches the removed text.

### 2.2 Time and memory limits (code)

| Item | Limit | Source |
|---|---|---|
| Verify job | 870 min on `[self-hosted, Linux, X64, qrh-proof]` (was 330 min on GitHub-hosted at 1dee293b) | `.github/workflows/pr-admission.yml:69`, `:75` |
| Replay budget | `QRH_REPLAY_BUDGET_SECONDS=43200` (12 h). Code default for other entry points 10800 s, max 43200 | `pr-admission.yml:79`; `verifier/worker_resources.py:10-12` |
| Threads, kernel jobs | `QRH_WORKER_THREADS=6`, `QRH_KERNEL_JOBS=1`. Threads get 2 GiB each; a kernel gets 8 GiB | `pr-admission.yml:80-81`; `worker_resources.py:47-62` |
| Setup of checker environment | 120 min | `pr-admission.yml:124-125` |
| Restore build cache | 10 min | `pr-admission.yml:128` |
| Preflight | 300 s | `verifier/standard/replay.py:85`, `:89` |
| Challenge and solution compile and export | 600 s each | `replay.py:106-107`, `:173-174` |
| Each module compile (retry included) | 1800 s | `replay.py:156` |
| Kernel checks | 3600 s per checker in parallel. Serial total 10800 s (below) | `replay.py:179`; `verifier/standard/judge.py:42-49` |
| Sandbox memory | Compile share 75% of RAM. Checks memory_max 85%, memory_high 75%, 256 tasks | `replay.py:57`, `:147` |
| Prepare and admission jobs | 10 min each | `pr-admission.yml:26`, `:178` |
| Per-folder source caps | 2 MiB per `.lean`, 64 MiB and at most 8191 files per folder | `verifier/manifest.mjs:68-73` |
| Dependency-closure caps | 16384 files and 128 MiB across the closure; 8192 per folder | `verifier/standard/prepare.mjs:62-63`, `:85-86` |

Kernel allowance (commit c1fa265f): `judge.py:42-49`. With one kernel job, the timeout is `timeout * (1 + len(v.protected_kernels(bundled)))`. That is 3600 × 3 = 10800 s for Lean default, nanoda and con-ron run in sequence under one shared deadline. With two or more kernel jobs, each check gets 3600 s concurrently. Test: `tests/parallel-judge.test.mjs`. The upstream admission workflow sets `QRH_KERNEL_JOBS: "1"` (`pr-admission.yml:81`), so the serial path applies.

### 2.3 Runner (`infra/actions-runner/README.md`)

- Two independent slots, each with 6 CPUs and 24 GiB (`:8`). Per-slot memory 26 GiB with no swap, 512 processes, 80 GiB guest disk (`:28-30`).
- Each job runs in a fresh KVM guest. The guest reaches the network only through an allowlisted proxy (`:33-34`; `proxy.py:31-51`).
- Idle guest expires after 1 hour. Absolute lifetime 16 hours (`:39-41`).

### 2.4 Mathlib cache policy

- Pins: toolchain `leanprover/lean4:v4.34.1` (`verifier/pins.json`). Mathlib `d13f23b7…` and PrimeNumberTheoremAnd `c39a7511…` (`verifier/standard/lake-manifest.json`). Packages are cloned at exact revisions (`verifier/actions/setup.py:24-31`).
- Official cache: `lake exe cache get` (`setup.py:76-77`). The only Mathlib host allowed by the proxy is `cache.mathlib.org` (`infra/actions-runner/proxy.py:43`, added in 65a8a3a4; `test_proxy.py:18`, `:30`).
- Submissions may import Mathlib. Package imports are limited to `PrimeNumberTheoremAnd` and `RellichKondrachov` (`setup.py:80-91`; `verifier/standard/prepare.mjs:138-139`).
- Ours: `/home/user/lean-env/qrh` has the same toolchain and the same Mathlib and PNT revisions.

### 2.5 Dependencies: build and reuse

- Build: the whole import closure of `Candidate.Main` is compiled from the PR head (`verifier/submission-dependencies.mjs:88-90`; `verifier/standard/prepare.mjs:55-76`). Each dependency tree must equal its tree at the source commit (`prepare.mjs:68-76`). The contract records `submission_trees` (`:129-131`).
- Signed build cache `submission-build-cache-v1` (README:150-154): compiled modules are reused, keyed by source, imports, compiler and libraries. A replay still runs Comparator and all three kernels. The cache is authenticated before use (`replay.py:113-125`).
- Receipts (README:156-195): a maintainer approves reuse of an earlier independent verification, for one exact head, bound and contract (`verifier/receipt-reuse.mjs:78-150`). A receipt does not transfer to another PR or to a dependent submission.
- Stale approvals (checked): the reuse approvals for PRs 71, 73 and 76 carry `policy_sha256` `b8bf491d…`. I reproduced that hash at commits c733be65 and b5a7a21e. Upstream now computes `5fa0aa65…`. Nine commits touching policy-scope paths have landed since b5a7a21e, including 4ac28350 and c1fa265f. Per README:192-194, stale approvals fail closed. Renewal needs maintainer review (README:184-185). Merged PRs are not re-checked (`verifier/check-pr.mjs:54-59`), so nothing breaks today.

### 2.6 Result-PR rules

- Declaration fields (`verifier/pr-admission.mjs:16-47`): `QRH-Result` must match `^[a-z][a-z0-9-]{2,63}$` (`:28`). `QRH-Bound` must be a reduced fraction: `core/rational.mjs` throws `Rational must be normalized.` for a non-reduced input (reached through `pr-admission.mjs:41`). `QRH-Decimal` is parsed at `:44-45`.
- A result PR changes only its own folder (`:146-163`). It cannot be mixed with maintenance changes (`:129-130`).
- Folder ID must equal `QRH-Result` (`:150-152`).
- Decimal rule (`verifier/pr-decimal.mjs:7`): `^(?:0|[1-9]\d{0,199})\.\d{1,200}$`. It must equal the truncated bound (`:52-73`). It must differ from the best `framework-verified` record (`:77-120`, message `needs more digits to differ`).
- Publication (`verifier/publication-record.mjs`): the ID must be new (`:79-84`, `Result ID already published`). Each `builds_on` ID must be published with an earlier `timeline_at` (`:85-91`, `Unknown or later catalogue predecessor`). `timeline_at` is the PR `created_at` (`:55`). The same predecessor rule is in `core/catalogue.mjs:137-140`.
- Accepted worker report (`verifier/worker-report.mjs:10-14`): target `QRH.canonical_bound`, kernels `Lean default`, `nanoda`, `con-ron`, and axioms `Classical.choice`, `Quot.sound`, `propext`.

---

## 3. Current leaderboard (top 8)

Method: admission archive branch `upstream/admission-records` (32 records) plus legacy `theta` values in metadata, sorted by exact value. This is offline. The live catalogue is generated and gitignored, so confirm on the site.

| # | Exact bound | Decimal | Folder (upstream/main) | Authors | PR (created, UTC) |
|---|---|---|---|---|---|
| 1 | 4369779/5000000 | 0.8739558 | `2026-10-28-density-split-fine-chain` | Jacob Sussman | #86 (2026-10-28) |
| 2 | 873981/1000000 | 0.873981 | `2026-10-28-density-split-fourth` | Rohan Arun | #85 (2026-10-28) |
| 3 | 174797/200000 | 0.873985 | `2026-10-27-density-split-third` | Rohan Arun | #84 (2026-10-27) |
| 4 | 174799/200000 | 0.873995 | `2026-10-26-sil-density-split` | Sil | #83 (2026-10-26) |
| 5 | 349843/400000 | 0.8746075 | `2026-10-25-arvi-repeated-marks-on-sil-face` | ArviFoxy | #76 (2026-10-25) |
| 6 | 1749387/2000000 | 0.8746935 | `2026-10-25-sil-fourth-power` | Sil | #74 (2026-10-25) |
| 7 | 8747289/10000000 | 0.8747289 | `2026-10-25-arvi-repeated-marks` | ArviFoxy | #73 (2026-10-25) |
| 8 | 21869322649/25000000000 | 0.87477290596 | `2026-10-24-slayer-recost-0p87477290596` | Slayer | #71 (2026-10-24) |

Context: #70 Mark Lewko `0.874772906` (2026-10-23), #69 Hailey Collet `0.8747729897` (2026-10-21). Folder date equals PR UTC date for all top 8.

---

## 4. IDs, dependencies and builds_on

ID formation:
- Legacy folders keep the ID from `verifier/submission-directories.json`, including any date suffix. Examples: `2026-10-25-arvi-repeated-marks-on-sil-face` → `arvi-repeated-marks-on-sil-face-20261025` (`:6`); `2026-10-26-sil-density-split` → `sil-density-split-20261026` (`:34`).
- The suffix need not match the folder date. `2026-10-27-density-split-third` → `density-split-third-20261026` (`:13`); `2026-10-25-arvi-repeated-marks` → `arvi-repeated-marks-20261024` (`:5`).
- New folders: the ID is the slug. `2026-10-28-density-split-fourth` → `density-split-fourth`.

For a new folder `2026-10-29-arvi-<name>`:
- ID: `arvi-<name>`, matching `^[a-z][a-z0-9-]{2,63}$`.
- Lean namespace: `Submissions.arvi_<name with _>`. Shared modules go in `src/Submissions/arvi_<name with _>/`.
- `QRH-Result: arvi-<name>`.
- The folder date must be the UTC date when the PR is opened. Today is 2026-10-28, so a PR opened today must be `2026-10-28-…`.
- The slug must not contain a date token. `arvi-<name>-20261029` is rejected.
- IDs listed in `submission-directories.json` are reserved for their original folders (`submission-paths.mjs:37-44`). Examples: `das-acyclic-bootstrap-874771265`, `count-affine-plain-20261014`.

References:
- `dependencies`: stable IDs of direct imports, keeping legacy suffixes. Example: `["arvi-repeated-marks-on-sil-face-20261025"]`.
  - `"2026-10-25-arvi-repeated-marks-on-sil-face"` fails the ID regex (probed: `Invalid submission dependencies`).
  - `"arvi-repeated-marks-on-sil-face"` resolves to no folder and fails with `Expected a regular submission arvi-repeated-marks-on-sil-face` (`submission-metadata.mjs:118`).
- `builds_on`: attribution. Each entry must be a published predecessor with an earlier PR time (`publication-record.mjs:85-91`). This is what the README calls "existing result IDs" (README:86-87).
- Example for a PR that imports only PR #86:
  ```json
  {
    "title": "…",
    "authors": [{ "name": "…" }],
    "description": "…",
    "builds_on": ["density-split-fine-chain", "sil-density-split-20261026", "arvi-repeated-marks-on-sil-face-20261025", "openai-baseline"],
    "dependencies": ["density-split-fine-chain"]
  }
  ```
- Closure size: PR #86's closure is 7813 files and 70.33 MiB, including itself. A new PR on top of it has roughly 58 MiB and 8500 files of headroom under the caps.

---

## 5. Our packaging script and checklist: what is out of date

Files: `research/mixed-step/package/make_submission.py` (ours), `CHECKLIST.md` (ours), plus `package_mixed.py`, `README.md`, `PR_BODY_DRAFT.md` and `Candidate/Main.lean` in the same folder.

### make_submission.py

| Line | Now | Needed |
|---|---|---|
| 3-4, 16 | Layout `DEST/src/Submissions/arvi_mixed_step_20261026/…` | `src/Submissions/arvi_mixed_step/…` (ID `arvi-mixed-step`) |
| 10-12 | DEST is `submissions/arvi-mixed-step-20261026` | `submissions/2026-MM-DD-arvi-mixed-step`, where the date is the UTC PR creation date. The old name fails the date-token rule |
| 18 | `PKG = 'Submissions.arvi_mixed_step_20261026'` | `Submissions.arvi_mixed_step` |
| 19, 35-36 | `DEV = 'Submissions.arvi_mixed_step.'`; a closure that starts with DEV aborts | Collides with the new PKG, so the guard would reject our own modules. Rename the dev prefix |
| 22 | `IMPORT = r'^import\s+(\S+)'` | Narrower than the verifier's `leanImports` (`verifier/actions/imports.mjs:43-47`), which accepts indentation, `public`, `meta`, `private`, and several names per line. The current closure has no misses (checked), but the rule is wider |
| 39-40 | Only the PKG prefix is followed; other submissions' imports are not checked | Every `Submissions.<other>` prefix must match a declared `dependencies` ID (`submission-dependencies.mjs:72-77`) |
| 80 | Copies `metadata.json` without validation | Run `validateSubmissionMetadata` (`submission-metadata.mjs:14`) and `submissionDependencies` (`submission-dependencies.mjs:5`) |
| 81 | Prints MB only | Enforce 2 MiB per `.lean`, 64 MiB and 8191 files per folder (`manifest.mjs:68-73`), and the closure caps (`prepare.mjs:62-63`, `:85-86`) |
| (missing) | No module-name check | `^(?:Candidate\|Submissions)(?:\.[A-Za-z_][A-Za-z0-9_]*)+$` (`replay.py:138`) |
| 35-38 | PR 76 return guard | Still correct. ID `arvi-repeated-marks-on-sil-face-20261025` is retained, and PR 76's folder contains `ReturnD` and `FinalReturn` |

Current sizes (ours): closure of 295 modules, 4.92 MiB, largest module 86 KiB. Adding PR 76's closure (7179 files, 61.13 MiB) gives roughly 66 MiB and 7476 files, within the 128 MiB and 16384-file caps.

### package_mixed.py

- Lines 19-23 (`DEV`, `RET`, `TARGET`, `TREES`): the target must become `Submissions.arvi_mixed_step`. The dev tree must be renamed so the two prefixes cannot overlap. The lakefile globs `Submissions.+` (`/home/user/lean-env/qrh/lakefile.lean`), so both trees would be built together.
- Line 24 and line 91: the same narrow import regex. `public`, `private` and `meta` imports are not rewritten.
- Precondition: `/home/user/lean-env/qrh/Submissions/arvi_mixed_step_20261026/Source/` is missing (the file exists in the dev tree). `make_submission.py` therefore aborts with `missing module`. Re-run `package_mixed.py` first.
- Scale: about 507 lines in the dev tree use `Submissions.arvi_mixed_step.`, and 619 import lines in the target tree use the old prefix. The docstring comment at `Graph/Endpoint3.lean:6` also names the old prefix.

### CHECKLIST.md

| Line | Now | Needed |
|---|---|---|
| 23-25 | Package `Submissions.arvi_mixed_step_20261026` | `Submissions.arvi_mixed_step` |
| 30-31 | `metadata.json` passes the validator | Still true (probed). Add: `dependencies` equals the direct imports, and each `builds_on` is a published, earlier predecessor |
| 33 | "within the hosted budget" | Name the budget: 12 h replay, 30 min per module, 3 h serial checking, 120 min setup, 870-min job. Cite `pr-admission.yml:75`, `replay.py:156`, `:179`, `infra/actions-runner/README.md:8-13` |
| 34-35 | Branch based on main; PR 76 "byte-identical"; all changes under `submissions/arvi-mixed-step-20261026/` | Compare with `submissions/2026-10-25-arvi-repeated-marks-on-sil-face/`. Only the new dated folder may change (`pr-admission.mjs:146-163`) |
| 36 | "no session links anywhere" | Conflicts with the attribution lines this session adds to commits and PRs. Decide which applies before committing |
| 16-20 | Numbers | Still arithmetically right, but see section 6 on position |
| 32 | Canonical wrapper compiles | Still right. Statement shape matches `verifier/upstream-challenge.lean:8-10` |

### PR_BODY_DRAFT.md

- Line 1: `QRH-Result: arvi-mixed-step-20261026` must be `QRH-Result: arvi-mixed-step`. The folder ID must match (`pr-admission.mjs:150-152`).
- Line 8: "current verified bound: 0.8746075 (PR #76, ours)" is stale. The best is 0.8739558 (PR #86). PRs #83-#85 are also below 0.8746075.
- The template checklist (`PULL_REQUEST_TEMPLATE.md:21-31`) is missing. Not enforced by code, but the template asks for it.

### README.md (package folder)

- Lines 3 and 16: the folder and namespace names are outdated.
- Lines 28-29: "the branch stacks on PR 76's submission branch" contradicts README:46 ("Start from the current `main` branch") and CHECKLIST.md:34. PR 76 is merged (01c21abe), so stacking is unnecessary.

### Candidate/Main.lean and metadata.json (ours)

- `Candidate/Main.lean` lines 7-8 import `Submissions.arvi_mixed_step_20261026.*`. These must become `Submissions.arvi_mixed_step.*`.
- `metadata.json` needs no change. It passes `validateSubmissionMetadata`, and its `builds_on` and `dependencies` use correct legacy IDs.

---

## 6. Other findings

- Branch base: our branches diverged at 1dee293b and still use pre-migration folder names. Branch from `upstream/main`.
- Bound position: 437037/500000 (0.874074) passes the decimal rule. Against the previous best 0.8739558 it differs at the third decimal (`0.873` versus `0.874`). It would be admitted and rank 5th, but it is not the frontier. The site frontier is PR #86.
- Reuse for our own package: no approval exists for the new package. Its verification must run in full, or a maintainer must register it.
- Build time: the 12-hour replay budget includes compiling the dependency closure (PR 76, Hailey Collet, OpenAI baseline) unless the signed cache has those modules. Our checklist should say whether the cache covers them.
