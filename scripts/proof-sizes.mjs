// Combine the committed per-proof metrics into the file the site loads.
import { execFileSync } from "node:child_process";
import { existsSync, readdirSync, readFileSync } from "node:fs";
import { join } from "node:path";
import { sizeEntry, validateMetrics } from "../core/proof-size.mjs";

// Metrics describe the exact sources they were measured on.
function sourceTree(root, id) {
  try {
    return execFileSync(
      "git",
      ["-C", root, "rev-parse", `HEAD:submissions/${id}/src`],
      { encoding: "utf8", stdio: ["ignore", "pipe", "ignore"] },
    ).trim();
  } catch {
    return null;
  }
}

export function buildSizes(
  root = process.cwd(),
  { onStale = console.warn } = {},
) {
  const directory = join(root, "metrics");
  const empty = { schema_version: 1, entries: {} };
  if (!existsSync(join(directory, "profile.json"))) return empty;
  const profile = JSON.parse(
    readFileSync(join(directory, "profile.json"), "utf8"),
  );
  const entries = {};
  for (const name of readdirSync(directory).sort()) {
    if (!name.endsWith(".json") || name === "profile.json") continue;
    const metrics = validateMetrics(
      JSON.parse(readFileSync(join(directory, name), "utf8")),
    );
    if (name !== `${metrics.result_id}.json`)
      throw Error(`Metrics file name differs from its result: ${name}`);
    if (metrics.profile !== profile.id)
      throw Error(`Metrics were measured under another profile: ${name}`);
    const current = sourceTree(root, metrics.result_id);
    // A measurement of other sources must not be shown against these.
    if (current && current !== metrics.source_tree) {
      onStale(`Ignoring stale proof metrics: ${metrics.result_id}`);
      continue;
    }
    entries[metrics.result_id] = sizeEntry(metrics);
  }
  const { id, lean_version, machine, workers, noise, modules_measured } =
    profile;
  return {
    schema_version: 1,
    profile: { id, lean_version, machine, workers, noise, modules_measured },
    entries,
  };
}
