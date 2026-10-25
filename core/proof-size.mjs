// Ways to size a proof, and the metrics files that record them.
// Each submission has metrics/<result-id>.json, written by bench/aggregate.py.
export const BASELINE_ID = "openai-baseline";

const compact = new Intl.NumberFormat("en-US", {
  notation: "compact",
  maximumFractionDigits: 1,
});
export const formatCount = (n) => compact.format(n);
export function formatDuration(seconds) {
  if (seconds < 90) return `${Math.round(seconds)} s`;
  const minutes = Math.round(seconds / 60);
  if (minutes < 60) return `${minutes} min`;
  const hours = seconds / 3600;
  return hours < 10 ? `${+hours.toFixed(1)} h` : `${Math.round(hours)} h`;
}
export function formatBytes(bytes) {
  const [unit, name] =
    bytes >= 2 ** 30
      ? [2 ** 30, "GiB"]
      : bytes >= 2 ** 20
        ? [2 ** 20, "MiB"]
        : [2 ** 10, "KiB"];
  return `${+(bytes / unit).toFixed(1)} ${name}`;
}
// Axis ticks are round numbers of whichever unit reads best: 30 s, 20 min, 5 h.
const seconds = [
  { size: 1, max: 59 },
  { size: 60, max: 59 },
  { size: 3600, max: 900 },
];
const sizes = [2 ** 10, 2 ** 20, 2 ** 30].map((size) => ({ size, max: 900 }));
const counts = [1, 1e3, 1e6, 1e9].map((size) => ({ size, max: 900 }));

export const measures = [
  {
    id: "cpu",
    label: "Compile CPU time",
    short: "CPU time",
    value: (e) => e.cpu_seconds,
    format: formatDuration,
    units: seconds,
    note: "CPU seconds to compile every module of the proof once from scratch, not counting what every file pays however small: importing its dependencies and starting up. Mathlib and the pinned libraries are prebuilt.",
  },
  {
    id: "cpu-own",
    label: "Compile CPU time beyond the OpenAI baseline",
    short: "CPU time beyond baseline",
    value: (e) => e.cpu_seconds_excluding_baseline,
    format: formatDuration,
    units: seconds,
    note: "The same measure without the OpenAI baseline that nearly every proof builds on: what a submission adds to the shared foundation.",
  },
  {
    id: "gzip",
    label: "Gzipped active source",
    short: "Gzipped source",
    value: (e) => e.gzip_bytes,
    format: formatBytes,
    units: sizes,
    note: "The Lean source reachable from the proof root, as the verifier compiles it: the modules Candidate.Main imports, transitively, without comments or layout, gzipped. Mathlib and the pinned libraries are not included. Unused files in a submission do not count.",
  },
  {
    id: "active",
    label: "Active source, uncompressed",
    short: "Active source",
    value: (e) => e.active_bytes,
    format: formatBytes,
    units: sizes,
    note: "The same text before gzip. Repetition makes it larger than it is hard to write down, which is what compression removes.",
  },
  {
    id: "memory",
    label: "Peak memory",
    short: "Peak memory",
    value: (e) => e.peak_rss_bytes,
    format: formatBytes,
    units: sizes,
    note: "Largest resident set of any single compile. It includes the memory-mapped Mathlib libraries every compile loads.",
  },
  {
    id: "modules",
    label: "Lean modules",
    short: "Modules",
    value: (e) => e.modules,
    format: formatCount,
    units: counts,
    note: "Modules in the import closure of the proof, as compiled by the verifier. Counts files, not their content.",
  },
  {
    id: "lines",
    label: "Lines of Lean",
    short: "Lines",
    value: (e) => e.lines,
    format: formatCount,
    units: counts,
    note: "Lines of source in those modules. Easy to change without changing the proof, so it is shown for comparison.",
  },
];
export const measureById = (id) => measures.find((m) => m.id === id);

const sha = /^[a-f0-9]{40}$/;
const count = (n) => Number.isSafeInteger(n) && n >= 0;
const amount = (x) => typeof x === "number" && Number.isFinite(x) && x >= 0;
export function validateMetrics(m) {
  const fail = (what) => {
    throw Error(`Invalid proof metrics for ${m?.result_id}: ${what}`);
  };
  if (
    m?.schema_version !== 1 ||
    !/^[a-z][a-z0-9-]{2,63}$/.test(m.result_id ?? "")
  )
    fail("identity");
  if (!sha.test(m.source_tree ?? "") || typeof m.profile !== "string")
    fail("source or profile");
  if (
    typeof m.dependency_trees !== "object" ||
    Object.values(m.dependency_trees).some((tree) => !sha.test(tree))
  )
    fail("dependency trees");
  if (![m.modules, m.lines, m.bytes].every(count)) fail("source totals");
  for (const key of ["active_bytes", "gzip_bytes"])
    if (m[key] !== undefined && !count(m[key])) fail(key);
  const c = m.compile;
  if (c !== undefined) {
    if (
      !amount(c.cpu_seconds) ||
      !amount(c.gross_cpu_seconds) ||
      !count(c.peak_rss_bytes) ||
      !Object.values(c.cpu_seconds_by_submission ?? {}).every(amount)
    )
      fail("compile cost");
    // Each part is rounded on its own, so allow a little for the sum.
    const parts = Object.values(c.cpu_seconds_by_submission);
    if (
      Math.abs(parts.reduce((a, b) => a + b, 0) - c.cpu_seconds) >
      0.1 * parts.length
    )
      fail("compile cost does not add up");
  }
  return m;
}

// What the site needs from a metrics file, keyed by the measures above.
export function sizeEntry(m) {
  const c = m.compile;
  return {
    modules: m.modules,
    lines: m.lines,
    ...(m.active_bytes !== undefined && { active_bytes: m.active_bytes }),
    ...(m.gzip_bytes !== undefined && { gzip_bytes: m.gzip_bytes }),
    ...(c && {
      cpu_seconds: c.cpu_seconds,
      cpu_seconds_excluding_baseline: +(
        c.cpu_seconds - (c.cpu_seconds_by_submission[BASELINE_ID] ?? 0)
      ).toFixed(1),
      peak_rss_bytes: c.peak_rss_bytes,
    }),
  };
}
