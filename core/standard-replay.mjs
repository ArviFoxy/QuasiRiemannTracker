import { lstatSync, readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";
import { createHash } from "node:crypto";
import { isDeepStrictEqual } from "node:util";
import { standardChallenge } from "./standard-challenge.mjs";
const hash = (b) => createHash("sha256").update(b).digest("hex");
const same = isDeepStrictEqual;
const demand = (ok, why) => {
  if (!ok) throw Error(`Standard replay: ${why}`);
};
const safe = (p) =>
  typeof p === "string" &&
  /^[A-Za-z0-9_./-]+$/.test(p) &&
  !p.startsWith("/") &&
  p.split("/").every((x) => x && x !== "." && x !== "..");
function files(root, prefix = "") {
  return readdirSync(join(root, prefix))
    .sort()
    .flatMap((name) => {
      const relative = prefix ? `${prefix}/${name}` : name,
        stat = lstatSync(join(root, relative));
      demand(safe(relative) && !stat.isSymbolicLink(), "unsafe evidence path");
      if (stat.isDirectory()) return files(root, relative);
      demand(stat.isFile(), "evidence must contain regular files");
      return [relative];
    });
}
export function validateStandardReplay(root, pin, contribution) {
  demand(
    safe(pin?.directory) &&
      pin.directory.startsWith("verifier/standard/receipts/"),
    "missing reviewed receipt",
  );
  let directory = root;
  for (const part of pin.directory.split("/")) {
    directory = join(directory, part);
    const stat = lstatSync(directory);
    demand(
      stat.isDirectory() && !stat.isSymbolicLink(),
      "unsafe evidence prefix",
    );
  }
  const bytes = (name) => readFileSync(join(directory, name));
  const json = (name) => JSON.parse(bytes(name));
  demand(
    hash(bytes("collection.json")) === pin.collection_sha256,
    "collection differs from reviewed pin",
  );
  const collection = json("collection.json");
  demand(
    collection.schema_version === 1 &&
      collection.kind === "standard-submission-replay",
    "wrong evidence kind",
  );
  demand(
    collection.files &&
      typeof collection.files === "object" &&
      !Array.isArray(collection.files),
    "invalid inventory",
  );
  demand(
    same(
      files(directory).sort(),
      [...Object.keys(collection.files), "collection.json"].sort(),
    ),
    "unlisted or missing evidence",
  );
  for (const [name, digest] of Object.entries(collection.files))
    demand(
      safe(name) && hash(bytes(name)) === digest,
      "artifact checksum mismatch",
    );
  const r = json("result.json"),
    c = json("contract.json"),
    config = json("comparator.json");
  demand(
    collection.files["result.json"] === pin.receipt_sha256,
    "receipt differs from reviewed run",
  );
  demand(
    r.status === "PASS" && r.judge_exit_code === 0,
    "proof was not accepted",
  );
  demand(
    r.reviewed_pr_head === c.head_sha &&
      r.source_repository === c.repository &&
      r.source_repository === contribution.repository &&
      (r.source_commit ?? r.reviewed_pr_head) === contribution.source_commit &&
      (r.source_commit ?? r.reviewed_pr_head) ===
        (c.source_commit ?? c.head_sha),
    "source revision differs",
  );
  demand(
    r.result_id === c.manifest.id && r.result_id === pin.result_id,
    "result ID differs",
  );
  demand(
    r.theta_exact ===
      `${c.manifest.theta.numerator}/${c.manifest.theta.denominator}` &&
      r.theta_exact === pin.theta_exact,
    "exact bound differs",
  );
  demand(
    same(r.targets, ["QRH.canonical_bound"]) &&
      same(config.theorem_names, r.targets) &&
      same(config.definition_names, []),
    "canonical target scope differs",
  );
  const axioms = ["Classical.choice", "Quot.sound", "propext"],
    kernels = ["Lean default", "nanoda", "con-ron"];
  demand(
    same(r.allowed_axioms, axioms) &&
      same(config.permitted_axioms, axioms) &&
      same(r.kernels, kernels),
    "kernel or axiom scope differs",
  );
  demand(
    same(Object.keys(config.external_kernels).sort(), ["con-ron", "nanoda"]),
    "external kernel configuration differs",
  );
  const challenge = standardChallenge(c.manifest.theta);
  demand(
    hash(Buffer.from(challenge)) === c.generated_files["Challenge.lean"] &&
      bytes("challenge-src/Challenge.lean").toString() === challenge,
    "canonical challenge differs",
  );
  const e = c.manifest.entrypoint;
  demand(
    /^Candidate(?:\.[A-Z][A-Za-z0-9_]*)+$/.test(e.module) &&
      /^[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)*$/.test(e.declaration),
    "invalid entrypoint",
  );
  const wrapper = `import ${e.module}\n\n${challenge.replace("import Mathlib\n", "").replace("  sorry", `  exact ${e.declaration} χ hs hpole`)}`;
  demand(
    hash(Buffer.from(wrapper)) === c.generated_files["Solution.lean"] &&
      bytes("solution-src/Solution.lean").toString() === wrapper,
    "standard solution wrapper differs",
  );
  demand(
    same(r.source_files, c.source_files) &&
      Object.keys(c.source_files).includes(
        `src/${e.module.replaceAll(".", "/")}.lean`,
      ),
    "checked source inventory differs",
  );
  demand(
    r.library_inventory_sha256 === c.library_inventory_sha256 &&
      /^[a-f0-9]{64}$/.test(r.library_inventory_sha256),
    "library snapshot binding differs",
  );
  const libraries = JSON.parse(
    readFileSync(join(root, "verifier/standard/library-pins.json"), "utf8"),
  );
  demand(
    Object.hasOwn(libraries, r.library_inventory_sha256),
    "unapproved library snapshot",
  );
  demand(
    r.driver_sha256 === pin.driver_sha256 &&
      hash(bytes("replay.py")) === pin.driver_sha256,
    "executed driver differs",
  );
  demand(
    r.palomar_sha256 ===
      "c575759d82c506f181b3736a110950fd32931c08a1be454262027d6205f178a2",
    "Palomar verifier differs",
  );
  demand(
    same(
      r.tool_pins,
      JSON.parse(
        readFileSync(join(root, "verifier/standard/tool-pins.json"), "utf8"),
      ),
    ),
    "checker tool pins differ",
  );
  demand(
    r.sandbox_preflight === "PASS" &&
      r.candidate_mount_preflight === "PASS" &&
      r.challenge_exported_before_candidate_execution === true &&
      r.receipt_outside_candidate === true,
    "isolation or challenge ordering missing",
  );
  demand(
    Number.isFinite(Date.parse(r.verified_at)),
    "missing verification time",
  );
  for (const [name, digest] of Object.entries(collection.files)) {
    if (name.startsWith("source/"))
      demand(
        r.source_files[name.slice(7)] === digest,
        "archived source binding differs",
      );
    else if (name !== "result.json" && name !== "replay.py")
      demand(r.artifacts[name] === digest, "receipt artifact binding differs");
  }
  const transcript = bytes("logs/judge.log").toString();
  demand(
    transcript.includes("Your solution is okay!") &&
      kernels.every((k) =>
        transcript.includes(`${k} kernel accepts the solution`),
      ),
    "incomplete kernel acceptance",
  );
  demand(
    !transcript.includes("--inadvisably-no-sandbox"),
    "checker sandbox was disabled",
  );
  const controls = json("controls.json");
  demand(
    same(
      controls.map((x) => x.expected),
      ["accepted", "statement-mismatch", "ill-typed-proof"],
    ),
    "missing checker controls",
  );
  for (const control of controls) {
    demand(
      safe(control.log) && Object.hasOwn(collection.files, control.log),
      "missing control transcript",
    );
    const text = bytes(control.log).toString();
    if (control.expected === "accepted")
      demand(
        control.exit_code === 0 &&
          kernels.every((k) =>
            text.includes(`${k} kernel accepts the solution`),
          ),
        "positive control failed",
      );
    if (control.expected === "statement-mismatch")
      demand(
        control.exit_code !== 0 &&
          text.includes(
            "Challenge and solution theorem statement do not match",
          ),
        "wrong statement rejection reason",
      );
    if (control.expected === "ill-typed-proof")
      demand(
        control.exit_code !== 0 &&
          text.includes("Lean default kernel rejected the solution"),
        "wrong proof rejection reason",
      );
  }
  return r;
}

export function validateStandardCatalogue(root, catalogue) {
  const pins = JSON.parse(
    readFileSync(join(root, "verifier/standard/catalogue-pins.json"), "utf8"),
  );
  for (const record of catalogue.records) {
    const reviewed = pins[record.id];
    if (!reviewed) {
      demand(
        record.status !== "framework-verified" ||
          !record.entrypoint?.module?.startsWith("Candidate."),
        "standard submission needs reviewed catalogue evidence",
      );
      continue;
    }
    const report = validateStandardReplay(
      root,
      reviewed.pin,
      reviewed.contribution,
    );
    const first = reviewed.first_pin
      ? validateStandardReplay(root, reviewed.first_pin, reviewed.contribution)
      : report;
    demand(
      same(first.source_files, report.source_files) &&
        same(first.tool_pins, report.tool_pins) &&
        first.theta_exact === report.theta_exact &&
        Date.parse(first.verified_at) <= Date.parse(report.verified_at),
      "first verification differs from current proof",
    );
    demand(
      record.status === "framework-verified" &&
        record.first_verified_at === first.verified_at &&
        record.repository === report.source_repository &&
        record.source_commit ===
          (report.source_commit ?? report.reviewed_pr_head),
      "catalogue verification identity differs",
    );
    demand(
      `${record.theta.numerator}/${record.theta.denominator}` ===
        report.theta_exact,
      "catalogue bound differs",
    );
    const contract = JSON.parse(
      readFileSync(join(root, reviewed.pin.directory, "contract.json"), "utf8"),
    );
    demand(
      same(record.entrypoint, contract.manifest.entrypoint),
      "catalogue entrypoint differs",
    );
    const source = join(root, "submissions", record.id);
    demand(
      lstatSync(source).isDirectory() && !lstatSync(source).isSymbolicLink(),
      "unsafe submission directory",
    );
    demand(
      same(files(source).sort(), Object.keys(report.source_files).sort()),
      "submission file set changed",
    );
    for (const [name, digest] of Object.entries(report.source_files))
      demand(
        hash(readFileSync(join(source, name))) === digest,
        "verified submission source changed",
      );
  }
}
