// Candidate commits supply data; validators and worker code come from the base.
import { execFileSync } from "node:child_process";
import { existsSync, readFileSync, mkdtempSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { isDeepStrictEqual } from "node:util";
import { validateCatalogue, boundLabel } from "../core/catalogue.mjs";
import {
  catalogueProofRecords,
  proofRevision,
} from "../core/catalogue-revisions.mjs";
import { validateSubmissionMetadata } from "./submission-metadata.mjs";
import { certificate } from "./certificate.mjs";

export function maintenancePaths(files) {
  return files
    .flatMap((f) => [
      f.filename,
      ...(f.previous_filename ? [f.previous_filename] : []),
    ])
    .some(
      (p) =>
        /^(submissions|proofs|public\/proofs|catalogue|public\/certificates|registry\/records)\//.test(
          p,
        ) ||
        ["public/catalogue.json", "public/registry.json"].includes(p) ||
        (/\.lean$/i.test(p) && !/^(verifier|core|tests)\//.test(p)),
    );
}

export function maintenancePlan({
  files,
  read,
  list,
  admittedCatalogue,
  readAdmittedCertificate,
}) {
  const oldBaseJSON = read("base", "catalogue/results.json");
  if (
    !oldBaseJSON &&
    files.some(
      (file) =>
        ["catalogue/results.json", "public/catalogue.json"].includes(
          file.filename,
        ) && file.status !== "removed",
    )
  )
    throw Error(
      "Catalogue JSON is generated output; edit proof metadata instead",
    );
  // Older commits have a tracked catalogue. New commits contain one metadata
  // file per legacy proof; current admissions come from the trusted archive.
  const baseMetadata = new Set(
    [...list("base", "proofs/"), ...list("base", "submissions/")]
      .filter(
        (path) =>
          /^(?:proofs|submissions)\/[^/]+\/metadata\.json$/.test(path) &&
          JSON.parse(read("base", path)).id,
      )
      .map((path) => path.split("/")[1]),
  );
  const oldBaseIds = new Set(
    oldBaseJSON
      ? catalogueProofRecords(JSON.parse(oldBaseJSON)).map(proofRevision)
      : [],
  );
  const archived = (
    admittedCatalogue ? catalogueProofRecords(admittedCatalogue) : []
  ).filter(
    (record) =>
      !baseMetadata.has(proofRevision(record)) &&
      !oldBaseIds.has(proofRevision(record)),
  );
  const archiveIds = new Set(archived.map(proofRevision));
  const metadataCatalogue = (side) => {
    const old = read(side, "catalogue/results.json");
    if (old) return JSON.parse(old);
    const records = [],
      historical_records = [];
    for (const path of [
      ...list(side, "proofs/"),
      ...list(side, "submissions/"),
    ].filter((path) =>
      /^(?:proofs|submissions)\/[^/]+\/metadata\.json$/.test(path),
    )) {
      const input = JSON.parse(read(side, path));
      if (!input.id) {
        validateSubmissionMetadata(input);
        continue;
      }
      const { historical, ...record } = input;
      if (path.split("/")[1] !== proofRevision(record))
        throw Error("Proof metadata path differs from its revision");
      (historical === true ? historical_records : records).push(record);
    }
    for (const record of archived) {
      if (
        [...records, ...historical_records].some(
          (entry) => proofRevision(entry) === proofRevision(record),
        )
      )
        throw Error(`Metadata duplicates an admitted proof: ${record.id}`);
      records.push(record);
    }
    return { schema_version: 1, records, historical_records };
  };
  const base = metadataCatalogue("base");
  const head = validateCatalogue(metadataCatalogue("head"));
  const old = new Map(
    catalogueProofRecords(base).map((r) => [proofRevision(r), r]),
  );
  const records = new Map(
    catalogueProofRecords(head).map((r) => [proofRevision(r), r]),
  );
  const required = new Map();
  const requireProof = (id) => {
    if (!/^[a-z][a-z0-9-]{2,63}$/.test(id))
      throw Error(`Invalid proof result ID: ${id}`);
    const record = records.get(id) || old.get(id);
    if (!record)
      throw Error(
        `Cannot determine the exact bound for ${id}; provide its proof metadata or a QRH result declaration`,
      );
    required.set(id, { result_id: id, theta_exact: boundLabel(record) });
  };
  const identity = (r) => [
    boundLabel(r),
    r.theta,
    r.bound_interval,
    r.status,
    r.repository?.toLowerCase(),
    r.source_commit,
    r.entrypoint,
    r.first_verified_at,
  ];
  for (const [id, record] of records) {
    if (
      !old.has(id) ||
      !isDeepStrictEqual(identity(old.get(id)), identity(record))
    )
      requireProof(id);
    if (record.status !== "framework-verified") continue;
    const name = `public/certificates/${id}.json`;
    if (record.certificate_url !== `certificates/${id}.json`)
      throw Error(`Missing verification record: ${id}`);
    const certificateData = (side) =>
      read(side, name) ||
      (archiveIds.has(id) ? readAdmittedCertificate?.(id) : null);
    const c = certificate(JSON.parse(certificateData("head")));
    if (
      c.result_id !== id ||
      c.theta_exact !== boundLabel(record) ||
      c.verified_at !== record.first_verified_at ||
      (record.source_commit && c.source_commit !== record.source_commit) ||
      (record.repository &&
        c.source_repository.toLowerCase() !==
          record.repository.toLowerCase()) ||
      !isDeepStrictEqual(c.bound_interval, record.bound_interval)
    )
      throw Error(`Verification record differs from catalogue: ${id}`);
    const previous = certificateData("base");
    if (previous) {
      const normalize = (value) => ({
        ...value,
        source_repository: value.source_repository.toLowerCase(),
      });
      if (
        !isDeepStrictEqual(
          normalize(certificate(JSON.parse(previous))),
          normalize(c),
        )
      )
        requireProof(id);
    }
  }
  const sourceIds = new Set();
  for (const f of files) {
    for (const path of [
      f.filename,
      ...(f.previous_filename ? [f.previous_filename] : []),
    ]) {
      const m = /^submissions\/([^/]+)\//.exec(path);
      if (m) sourceIds.add(m[1]);
      else if (
        /\.lean$/i.test(path) &&
        !/^(verifier|core|tests)\//.test(path) &&
        f.status !== "removed" &&
        path === f.filename
      )
        throw Error(
          `Place maintained proof source in submissions/<result-id>/src: ${path}`,
        );
    }
    if (
      f.filename.startsWith("public/certificates/") &&
      f.status !== "removed"
    ) {
      const c = certificate(JSON.parse(read("head", f.filename)));
      if (!records.has(c.result_id))
        throw Error(
          `Verification record has no catalogue result: ${c.result_id}`,
        );
    }
  }
  for (const id of sourceIds) {
    if (list("head", `submissions/${id}/`).length) requireProof(id);
  }
  if (
    files.some(
      (f) => f.filename === "public/catalogue.json" && f.status !== "removed",
    )
  ) {
    const published = JSON.parse(read("head", "public/catalogue.json"));
    if (!isDeepStrictEqual(published, head))
      throw Error("Published catalogue differs from catalogue/results.json");
  }
  if (required.size > 256)
    throw Error("A PR can validate at most 256 affected proofs");
  return [...required.values()].sort((a, b) =>
    a.result_id.localeCompare(b.result_id),
  );
}

export async function maintenanceVerification(root, { pr, files, repository }) {
  if (!maintenancePaths(files)) return [];
  if (
    !/^[\w.-]+\/[\w.-]+$/.test(repository) ||
    ![pr.base.sha, pr.head.sha].every((s) => /^[a-f0-9]{40}$/.test(s))
  )
    throw Error("Invalid maintenance validation identity");
  const directory = mkdtempSync(join(tmpdir(), "qrh-maintenance-"));
  const git = (args) =>
    execFileSync("git", ["-c", "core.hooksPath=/dev/null", ...args], {
      cwd: directory,
      encoding: "utf8",
      timeout: 300000,
      maxBuffer: 32 * 1024 ** 2,
      env: {
        PATH: process.env.PATH,
        GIT_CONFIG_NOSYSTEM: "1",
        GIT_CONFIG_GLOBAL: "/dev/null",
        GIT_TERMINAL_PROMPT: "0",
        GIT_NO_REPLACE_OBJECTS: "1",
        GIT_ALLOW_PROTOCOL: "https",
      },
      stdio: ["ignore", "pipe", "pipe"],
    });
  const refs = { base: pr.base.sha, head: pr.head.sha };
  const list = (ref, path) =>
    git(["ls-tree", "-r", "--name-only", refs[ref], "--", path])
      .trim()
      .split("\n")
      .filter(Boolean);
  const read = (ref, path) => {
    const entry = git(["ls-tree", refs[ref], "--", path]);
    if (!entry) return null;
    if (!/^100644 blob /.test(entry))
      throw Error(`Expected a regular data file: ${path}`);
    return git(["show", `${refs[ref]}:${path}`]);
  };
  try {
    git(["init", "--bare", "--template="]);
    git(["remote", "add", "origin", `https://github.com/${repository}.git`]);
    git(["config", "remote.origin.promisor", "true"]);
    git(["config", "remote.origin.partialclonefilter", "blob:none"]);
    git([
      "fetch",
      "--no-tags",
      "--filter=blob:none",
      "--depth=1",
      "origin",
      refs.base,
      refs.head,
    ]);
    const cataloguePath = join(root, "catalogue/results.json");
    return maintenancePlan({
      files,
      read,
      list,
      admittedCatalogue: existsSync(cataloguePath)
        ? JSON.parse(readFileSync(cataloguePath, "utf8"))
        : undefined,
      readAdmittedCertificate: (id) => {
        const path = join(root, `public/certificates/${id}.json`);
        return existsSync(path) ? readFileSync(path, "utf8") : null;
      },
    });
  } finally {
    rmSync(directory, { recursive: true, force: true });
  }
}
