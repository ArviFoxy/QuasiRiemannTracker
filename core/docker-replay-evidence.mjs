import { createHash } from "node:crypto";
import { lstatSync, readFileSync, readdirSync } from "node:fs";
import { join } from "node:path";

const sha = (bytes) => createHash("sha256").update(bytes).digest("hex");
const same = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const hash = (s) => typeof s === "string" && /^[a-f0-9]{64}$/.test(s);
const safe = (s) =>
  typeof s === "string" &&
  /^[A-Za-z0-9_./-]+$/.test(s) &&
  s.split("/").every((part) => part && part !== "." && part !== "..");
const demand = (ok, reason) => {
  if (!ok) throw Error(`Docker maintainer replay: ${reason}`);
};
const profiles = {
  "docker-classical-v1": {
    file: "classical-pins.json",
    bound: "1/1",
    result: "classical-euler-product",
    targets: ["QRH.canonical_bound", "QRH.zeta_bound"],
  },
  "docker-single-prime-v1": {
    file: "single-prime-pins.json",
    bound: "29/33",
    result: "single-prime-29-33-20261010",
    targets: [
      "SinglePrime2933.allDirichlet",
      "SinglePrime2933.zeta",
      "SinglePrime2933.allHecke",
    ],
  },
};

export function validateDockerReplay(root, pin, contribution) {
  const profile = profiles[pin?.replay_profile];
  demand(
    profile &&
      safe(pin.directory) &&
      pin.directory.startsWith("evidence/pr-checks/"),
    "unknown profile or unsafe evidence directory",
  );
  const readAt = (path) => {
    demand(safe(path), "unsafe evidence path");
    let current = root;
    const parts = path.split("/");
    for (let i = 0; i < parts.length; i++) {
      current = join(current, parts[i]);
      const stat = lstatSync(current);
      demand(
        !stat.isSymbolicLink() &&
          (i === parts.length - 1 ? stat.isFile() : stat.isDirectory()),
        "unsafe evidence file",
      );
    }
    return readFileSync(current);
  };
  const read = (name) => readAt(`${pin.directory}/${name}`);
  const list = (path) =>
    readdirSync(join(root, path))
      .sort()
      .flatMap((name) => {
        demand(safe(name), "unsafe inventory filename");
        const full = `${path}/${name}`,
          stat = lstatSync(join(root, full));
        demand(!stat.isSymbolicLink(), "symlink in evidence");
        return stat.isDirectory()
          ? list(full)
          : (demand(stat.isFile(), "special evidence file"), [full]);
      });
  demand(
    hash(pin.collection_sha256) &&
      sha(read("collection.json")) === pin.collection_sha256,
    "collection differs from reviewed pin",
  );
  const collection = JSON.parse(read("collection.json"));
  demand(
    collection.schema_version === 1 &&
      collection.kind === "independent-docker-maintainer-replay" &&
      collection.files &&
      !Array.isArray(collection.files),
    "invalid collection",
  );
  demand(
    same(
      list(pin.directory).sort(),
      [...Object.keys(collection.files), "collection.json"]
        .sort()
        .map((name) => `${pin.directory}/${name}`),
    ),
    "missing or unlisted evidence",
  );
  for (const [name, expected] of Object.entries(collection.files)) {
    demand(
      safe(name) && hash(expected) && sha(read(name)) === expected,
      "evidence checksum differs",
    );
    demand(
      !/\.(?:olean|export|ndjson|zip|gz)$/.test(name),
      "private build artifact in publication",
    );
  }
  demand(
    hash(pin.receipt_sha256) &&
      collection.files["result.json"] === pin.receipt_sha256,
    "receipt differs from reviewed pin",
  );
  const report = JSON.parse(read("result.json"));
  const prefix = "verifier/docker/";
  const inputsBytes = readAt(prefix + profile.file),
    inputs = JSON.parse(inputsBytes);
  demand(
    report.pins_sha256 === sha(inputsBytes) &&
      report.driver_sha256 === sha(readAt(prefix + "replay.py")) &&
      report.sandbox_sha256 === sha(readAt(prefix + "sandbox.py")),
    "reviewed runner or inputs differ",
  );
  if (report.source_replay) {
    demand(
      report.recheck_driver_sha256 === sha(readAt(prefix + "recheck.py")),
      "head recheck runner differs",
    );
    const oldBytes = read("original-source-replay/pins.json");
    const oldReportBytes = read("original-source-replay/result.json");
    const oldInputs = JSON.parse(oldBytes),
      oldReport = JSON.parse(oldReportBytes);
    demand(
      sha(oldBytes) === report.source_replay.pins_sha256 &&
        sha(oldReportBytes) === report.source_replay.receipt_sha256 &&
        oldReport.pins_sha256 === sha(oldBytes) &&
        !oldReport.source_replay &&
        oldReport.status === "PASS" &&
        oldReport.judge_exit_code === 0 &&
        oldReport.reviewed_pr_head === oldInputs.head_sha &&
        oldInputs.head_sha === report.source_replay.head_sha,
      "original source replay differs",
    );
    const { head_sha: oldHead, ...oldContent } = oldInputs;
    const { head_sha: newHead, ...newContent } = inputs;
    demand(
      same(oldContent, newContent),
      "head recheck changed source, target or tool pins",
    );
    for (const key of [
      "driver_sha256",
      "sandbox_sha256",
      "theta_exact",
      "targets",
      "kernels",
      "allowed_axioms",
    ])
      demand(
        same(oldReport[key], report[key]),
        "original replay scope differs",
      );
    const oldArtifacts = { ...oldReport.artifacts },
      newArtifacts = { ...report.artifacts };
    for (const name of ["judge.out", "judge.err"]) {
      demand(
        sha(read("original-source-replay/" + name)) ===
          oldArtifacts["logs/" + name],
        "original checker log differs",
      );
      delete oldArtifacts["logs/" + name];
      delete newArtifacts["logs/" + name];
    }
    demand(
      same(oldArtifacts, newArtifacts),
      "head recheck changed source replay artifacts",
    );
    demand(
      Date.parse(oldReport.verified_at) <= Date.parse(report.verified_at),
      "head recheck predates source replay",
    );
  }
  demand(
    report.status === "PASS" && report.judge_exit_code === 0,
    "independent checker acceptance required",
  );
  demand(
    report.theta_exact === profile.bound &&
      inputs.theta_exact === profile.bound &&
      report.result_id === profile.result &&
      inputs.result_id === profile.result &&
      same(report.targets, profile.targets) &&
      same(inputs.targets, profile.targets),
    "target scope differs",
  );
  demand(
    report.reviewed_pr_head === inputs.head_sha &&
      /^[a-f0-9]{40}$/.test(inputs.head_sha) &&
      report.source_repository === inputs.repository &&
      inputs.repository === contribution.repository &&
      inputs.head_sha === contribution.source_commit,
    "source head or repository differs",
  );
  demand(
    report.challenge_exported_before_candidate_execution === true &&
      report.receipt_outside_candidate === true &&
      report.isolation === "offline Docker" &&
      report.official_flag === "--inadvisably-no-sandbox" &&
      report.image === inputs.image,
    "isolation or challenge ordering differs",
  );
  demand(
    report.source_compiler === "4.34.1" &&
      report.judge_toolchain === "4.35.0-rc2" &&
      same(report.allowed_axioms, [
        "Classical.choice",
        "Quot.sound",
        "propext",
      ]) &&
      same(report.kernels, ["Lean default", "nanoda", "con-ron"]),
    "kernel or axiom scope differs",
  );
  demand(
    typeof report.verified_at === "string" &&
      Number.isFinite(Date.parse(report.verified_at)),
    "missing verification time",
  );
  demand(
    sha(readAt(prefix + inputs.challenge_file)) === inputs.challenge_sha256,
    "canonical challenge differs",
  );
  const candidate = Object.fromEntries(
    Object.values(inputs.candidate_sources).map((source) => [
      "candidate-src/" + source.destination,
      source.sha256,
    ]),
  );
  demand(
    same(
      Object.keys(report.artifacts)
        .filter((name) => name.startsWith("candidate-src/"))
        .sort(),
      Object.keys(candidate).sort(),
    ),
    "candidate source inventory differs",
  );
  for (const [name, expected] of Object.entries(report.artifacts)) {
    demand(safe(name) && hash(expected), "invalid receipt artifact");
    if (name.startsWith("candidate-src/"))
      demand(expected === candidate[name], "candidate source differs");
    else if (name.startsWith("exports/"))
      demand(
        ["exports/Challenge.export", "exports/Solution.export"].includes(name),
        "unknown private export",
      );
    else if (name === "challenge-src/Challenge.lean")
      demand(
        expected === inputs.challenge_sha256,
        "canonical challenge artifact differs",
      );
    else
      demand(collection.files[name] === expected, "receipt artifact differs");
  }
  for (const name of ["exports/Challenge.export", "exports/Solution.export"])
    demand(hash(report.artifacts[name]), "missing proof export hash");
  demand(
    report.artifacts["challenge-src/Challenge.lean"] ===
      inputs.challenge_sha256,
    "exported challenge source differs",
  );
  const config = JSON.parse(read("config/comparator.json"));
  demand(
    same(config.theorem_names, profile.targets) &&
      same(config.definition_names, []) &&
      same(config.permitted_axioms, report.allowed_axioms),
    "Comparator contract differs",
  );
  const transcript =
    read("logs/judge.out").toString() + read("logs/judge.err").toString();
  demand(
    transcript.includes("Your solution is okay!") &&
      report.kernels.every((kernel) =>
        transcript.includes(`${kernel} kernel accepts the solution`),
      ),
    "incomplete kernel transcript",
  );
  demand(
    read("logs/isolation-controls.out").toString().trim() ===
      "isolation-controls-pass",
    "isolation controls failed",
  );
  const phases = JSON.parse(read("phases.json"));
  demand(
    same(
      phases.map((phase) => phase.name),
      [
        "isolation-controls",
        "challenge-compile",
        "challenge-export",
        ...inputs.build_order.map((module) => "compile-" + module),
        "solution-export",
        "judge",
      ],
    ) &&
      phases.every(
        (phase) => phase.exit_code === 0 && phase.image === inputs.image,
      ),
    "replay phase failed or missing",
  );
  demand(
    sha(read("controls/control-results.json")) === inputs.controls_sha256 &&
      report.controls_sha256 === inputs.controls_sha256,
    "checker controls differ",
  );
  const controls = JSON.parse(read("controls/control-results.json"));
  demand(
    controls.status === "PASS" &&
      controls.image === inputs.image &&
      controls.sandbox_driver_sha256 === report.sandbox_sha256 &&
      controls.driver_sha256 === sha(readAt(prefix + "checker-controls.py")),
    "checker control runner differs",
  );
  demand(
    same(
      controls.cases.map(({ name, expected_exit_code, message }) => [
        name,
        expected_exit_code,
        message,
      ]),
      [
        ["PalomarPreflightSolution", 0, "Your solution is okay!"],
        [
          "PalomarPreflightWrong",
          1,
          "Challenge and solution theorem statement do not match",
        ],
        [
          "PalomarPreflightIllTyped",
          1,
          "Lean default kernel rejected the solution",
        ],
      ],
    ) &&
      controls.cases.every(
        (control) => control.result.exit_code === control.expected_exit_code,
      ),
    "checker controls failed for an unexpected reason",
  );
  for (const control of controls.cases) {
    const transcript =
      read(`controls/logs/judge-${control.name}.out`).toString() +
      read(`controls/logs/judge-${control.name}.err`).toString();
    demand(
      control.result.image === inputs.image &&
        transcript.includes(control.message),
      "checker control transcript has the wrong rejection reason",
    );
    if (control.expected_exit_code === 0)
      demand(
        report.kernels.every((kernel) =>
          transcript.includes(`${kernel} kernel accepts the solution`),
        ),
        "positive control is missing kernel acceptance",
      );
  }
  return report;
}

export function validateDockerCatalogue(root, catalogue) {
  const policy = JSON.parse(
    readFileSync(join(root, "verifier/pr-admissions.json")),
  );
  for (const [name, profile] of Object.entries(profiles)) {
    const record = catalogue.records.find(
      (record) => record.id === profile.result,
    );
    if (!record || record.status === "verification-pending") continue;
    const entries = policy.admissions.filter(
      (entry) => entry.pin.replay_profile === name,
    );
    demand(
      entries.length === 1,
      "catalogue verification requires its independent admission",
    );
    const entry = entries[0],
      report = validateDockerReplay(root, entry.pin, entry.contribution);
    demand(
      `${record.theta.numerator}/${record.theta.denominator}` ===
        report.theta_exact,
      "catalogue bound differs from the checked theorem",
    );
    const inputs = JSON.parse(
      readFileSync(join(root, "verifier/docker", profile.file)),
    );
    for (const [path, expected] of Object.entries(inputs.candidate_sources)) {
      demand(safe(path), "unsafe candidate source path");
      let file = root;
      for (const part of path.split("/")) {
        file = join(file, part);
        demand(!lstatSync(file).isSymbolicLink(), "candidate source symlink");
      }
      demand(
        lstatSync(file).isFile() && sha(readFileSync(file)) === expected.sha256,
        "catalogue proof source differs from independent replay",
      );
    }
    if (record.status === "framework-verified") {
      demand(
        record.repository === report.source_repository &&
          Number.isFinite(Date.parse(record.first_verified_at)) &&
          Date.parse(record.first_verified_at) <=
            Date.parse(report.verified_at),
        "catalogue verification date or attribution differs",
      );
    }
  }
}
