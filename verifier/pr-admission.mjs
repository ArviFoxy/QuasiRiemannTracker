// This module must be loaded from the trusted base checkout, never from a PR.
import { rational, cmp, BASELINE } from "../core/rational.mjs";
import { validateAdmission } from "./pr-evidence.mjs";

export function parseDeclaration(body) {
  const fields = new Map();
  for (const line of (body ?? "").split(/\r?\n/)) {
    if (!line.trim().startsWith("QRH-")) continue;
    const match = /^QRH-(Type|Result|Bound): ([^\r\n]+)$/.exec(line.trim());
    if (!match) throw Error("Malformed or unknown QRH declaration field");
    if (fields.has(match[1])) throw Error("Duplicate QRH declaration field");
    fields.set(match[1], match[2].trim());
  }
  const type = fields.get("Type");
  if (!["maintenance", "new-bound"].includes(type))
    throw Error(
      "Declare QRH-Type: maintenance or QRH-Type: new-bound in the PR body",
    );
  if (type === "maintenance") {
    if (fields.size !== 1)
      throw Error("Maintenance must not declare a result or bound");
    return { type };
  }
  const result_id = fields.get("Result"),
    theta_exact = fields.get("Bound");
  if (!/^[a-z][a-z0-9-]{2,63}$/.test(result_id ?? ""))
    throw Error("New bounds require QRH-Result: <stable-result-id>");
  if (
    !theta_exact ||
    theta_exact.length > 256 ||
    /[\x00-\x1f\x7f]/.test(theta_exact)
  )
    throw Error("New bounds require QRH-Bound: <exact checked value>");
  // Rational literals must be canonical. Algebraic expressions are compared
  // byte-for-byte with the trusted replay's exact bound; never evaluated here.
  if (/^[\d\s+./-]+$/.test(theta_exact)) {
    const match = /^(\d+)\/(\d+)$/.exec(theta_exact);
    if (!match)
      throw Error("Use an exact reduced fraction, not a decimal bound");
    const value = rational(match[1], match[2]);
    if (BigInt(value.numerator) <= 0n || cmp(value, BASELINE) > 0)
      throw Error("Bound must be positive and at most 7/8");
  }
  return { type, result_id, theta_exact };
}

function proofPath(name) {
  return (
    /^(?:proofs|public\/proofs|submissions|catalogue|registry\/records)(?:\/|$)/.test(
      name,
    ) ||
    ["public/catalogue.json", "public/registry.json"].includes(name) ||
    (/\.lean$/i.test(name) && !/^(?:verifier|core|tests)\//.test(name))
  );
}

function paths(files) {
  return files.flatMap((file) => {
    if (typeof file.filename !== "string" || !file.filename)
      throw Error("Invalid changed-file response");
    if (file.status === "renamed" && !file.previous_filename)
      throw Error("Renamed file is missing its previous path");
    return [
      file.filename,
      ...(file.previous_filename ? [file.previous_filename] : []),
    ];
  });
}

export function classifyChanges(files) {
  return paths(files).some(proofPath);
}

export async function evaluatePR({
  pr,
  files,
  repository,
  defaultBranch,
  root,
  validateEvidence = validateAdmission,
}) {
  if (pr.base?.repo?.full_name !== repository || pr.base?.ref !== defaultBranch)
    throw Error(
      "Admission requires a PR targeting this repository's default branch",
    );
  if (
    !Number.isSafeInteger(pr.number) ||
    pr.number < 1 ||
    !/^[a-f0-9]{40}$/.test(pr.head?.sha ?? "")
  )
    throw Error("Invalid PR identity or head commit");
  if (pr.state !== "open" || pr.draft)
    throw Error("Admission requires an open, non-draft PR");
  if (
    !Array.isArray(files) ||
    !files.length ||
    files.length !== pr.changed_files ||
    new Set(files.map((f) => f.filename)).size !== files.length
  )
    throw Error(
      "Incomplete or duplicate PR file list; refusing a truncated diff",
    );
  const declaration = parseDeclaration(pr.body);
  const proofBearing = classifyChanges(files);
  if (declaration.type === "maintenance") {
    if (proofBearing)
      throw Error(
        "Proof, submission or catalogue changes require QRH-Type: new-bound and independently checked evidence",
      );
    return "Maintenance change: no proof or catalogue admission. Website checks and maintainer review are still required.";
  }
  if (!proofBearing)
    throw Error(
      "New-bound PR contains no proof, submission or catalogue changes",
    );
  if (paths(files).some((name) => !proofPath(name)))
    throw Error(
      "Separate proof changes from workflow, verifier and other infrastructure changes",
    );
  await validateEvidence(root, {
    repository,
    number: pr.number,
    head_sha: pr.head.sha,
    result_id: declaration.result_id,
    theta_exact: declaration.theta_exact,
  });
  return `Independent maintainer evidence accepts ${declaration.result_id} at ${declaration.theta_exact} for this exact PR head.`;
}
