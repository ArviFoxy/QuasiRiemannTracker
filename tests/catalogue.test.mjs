import test from "node:test";
import assert from "node:assert/strict";
import { readFileSync } from "node:fs";
import {
  validateCatalogue,
  verifiedHere,
  timelineRecords,
  historicalBaseline,
  statusLabel,
  formatContributionDate,
} from "../core/catalogue.mjs";
import { frontierHistory, recordHistory, cmp } from "../core/rational.mjs";
const data = () => JSON.parse(readFileSync("catalogue/results.json", "utf8"));
test("the existing contribution selects one current proof revision and preserves its earlier metadata", () => {
  const d = validateCatalogue(data());
  const current = d.records.filter((r) => r.id.startsWith("nielstron-"));
  assert.equal(current.length, 1);
  assert.equal(current[0].id, "nielstron-20261009-tightening");
  assert.equal(current[0].proof_revision, "nielstron-algebraic-20261009");
  assert.equal(d.historical_records.length, 1);
  assert.equal(
    d.historical_records[0].theta.numerator,
    "874957019420098946128604623",
  );
  assert.equal(
    d.historical_records[0].source_commit,
    "49331e02e2c04bb2388ae9c6e9ea424c23b96ac6",
  );
});
test("the plotted frontier retains the strongest bound while verification stays separate", () => {
  const d = validateCatalogue(data());
  const verified = d.records.filter(verifiedHere);
  assert.equal(verified.length, 10);
  const timeline = recordHistory(timelineRecords(verified));
  const frontier = frontierHistory(timeline, []);
  assert.equal(frontier.length, timeline.length);
  for (let i = 0; i < frontier.length; i++) {
    assert.equal(frontier[i].at, timeline[i].first_verified_at);
    assert.ok(cmp(frontier[i].theta, timeline[i].theta) <= 0);
    if (i) assert.ok(cmp(frontier[i].theta, frontier[i - 1].theta) <= 0);
  }
  const strongest = verified.reduce((best, r) =>
    cmp(r.theta, best.theta) < 0 ? r : best,
  );
  assert.equal(cmp(frontier.at(-1).theta, strongest.theta), 0);
  assert.ok(
    d.records
      .filter((r) => !verifiedHere(r))
      .every((r) => r.first_verified_at === ""),
  );
});
test("Liu's algebraic threshold is enclosed exactly; a truncated decimal is rejected", () => {
  const d = data();
  validateCatalogue(d);
  const liu = d.records.find((r) => r.id.startsWith("liu-"));
  liu.theta = { numerator: "874957069799", denominator: "1000000000000" };
  liu.bound_interval.upper = liu.theta;
  assert.throws(() => validateCatalogue(d), /enclosure/);
});
test("Cycle25 advances the boundary only after independent maintainer verification", () => {
  const d = validateCatalogue(data());
  const cycle = d.records.find((r) => r.id === "cycle25-quartic-20261010");
  assert.deepEqual(cycle.theta, {
    numerator: "683505193",
    denominator: "781250000",
  });
  assert.equal(cycle.status, "framework-verified");
  assert.equal(cycle.first_verified_at, "2026-10-10T16:09:09.733191+00:00");
  assert.equal(verifiedHere(cycle), true);
  assert.deepEqual(cycle.builds_on, [
    "openai-baseline",
    "akashlevy-20261009-weighted-numerator",
  ]);
  assert.equal(
    cycle.entrypoint.declaration,
    "Cycle25.dirichlet_nonzero_catalogue",
  );
  const frontier = frontierHistory(
    timelineRecords(
      d.records.filter(
        (r) =>
          verifiedHere(r) &&
          Date.parse(r.first_verified_at) <=
            Date.parse(cycle.first_verified_at),
      ),
    ),
    [],
  );
  assert.equal(cmp(frontier.at(-1).theta, cycle.theta), 0);
  assert.ok(cycle.references.some((r) => r.url.endsWith("/paper.pdf")));
  assert.ok(
    cycle.references.some((r) => r.url.endsWith("/source-public.tar.gz")),
  );
});
test("catalogue cannot fabricate signed admission or local verification dates for pending results", () => {
  const d = data();
  d.records[1].status = "verified";
  assert.throws(() => validateCatalogue(d), /Unsupported/);
  const e = data();
  e.records[1].status = "verification-pending";
  e.records[1].first_verified_at = "2026-10-09T00:00:00Z";
  assert.throws(() => validateCatalogue(e), /Pending result/);
});

const historicalCatalogue = () => {
  const d = data();
  const fixture = {
    ...d.records[0],
    id: "test-historical-baseline",
    proof_revision: undefined,
    status: "historical-baseline",
    theta: { numerator: "1", denominator: "1" },
    timeline_at: "1922-01-01T00:00:00Z",
    date_precision: "year",
    first_verified_at: "",
    receipt_url: "",
    log_url: "",
    builds_on: [],
  };
  d.records.push(fixture);
  return { data: d, baseline: fixture };
};
test("historical baseline preserves a year-only date and its separate status", () => {
  const { data: d, baseline } = historicalCatalogue();
  validateCatalogue(d);
  assert.equal(historicalBaseline(baseline), true);
  assert.equal(verifiedHere(baseline), false);
  assert.equal(statusLabel(baseline), "Historical baseline");
  assert.equal(formatContributionDate(baseline), "1922");
});
test("historical baseline validation enforces theta = 1 and historical evidence metadata", () => {
  for (const changes of [
    { first_verified_at: "2026-10-10T00:00:00Z" },
    { receipt_url: "proofs/fake-receipt.json" },
    { log_url: "proofs/fake-log.json" },
    { theta: { numerator: "7", denominator: "8" } },
  ]) {
    const { data: changed, baseline } = historicalCatalogue();
    Object.assign(baseline, changes);
    assert.throws(() => validateCatalogue(changed), {
      message:
        "Historical baseline must be theta = 1 without local or signed verification claims",
    });
  }
  const { data: changed, baseline } = historicalCatalogue();
  baseline.timeline_at = "1922-02-15T00:00:00Z";
  assert.throws(() => validateCatalogue(changed), {
    message: "Year-only dates must use the start-of-year plotting anchor",
  });
});
