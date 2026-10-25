import { test, expect, type Page } from "@playwright/test";
import { catalogue, record, routeCatalogue } from "./catalogue-fixture";

// The fixture bounds are 7/8 > 8749/10000 > 87489/100000. By compile CPU, alive
// code and the reachable modules the newest result is both stronger and smaller
// than the improvement, so only the baseline and the newest result are on the
// front. Uncompressed, every stronger bound costs more, so all three are.
const sizes = () => ({
  schema_version: 1,
  profile: {
    id: "profile0001",
    lean_version: "4.34.1",
    machine: { cpu: "Example CPU", cores: 4, memory_bytes: 17179869184 },
    workers: 3,
    modules_measured: 390,
  },
  entries: {
    "fixture-baseline": {
      alive_gzip_bytes: 120 * 1024,
      alive_bytes: 600 * 1024,
      gzip_bytes: 200 * 1024,
      active_bytes: 900 * 1024,
      cpu_seconds: 3600,
      cpu_seconds_excluding_baseline: 0.1,
      peak_rss_bytes: 4 * 2 ** 30,
    },
    "fixture-improvement": {
      alive_gzip_bytes: 180 * 1024,
      alive_bytes: 800 * 1024,
      gzip_bytes: 300 * 1024,
      active_bytes: 1200 * 1024,
      cpu_seconds: 10800,
      cpu_seconds_excluding_baseline: 7200,
      peak_rss_bytes: 5 * 2 ** 30,
    },
    "fixture-newest": {
      alive_gzip_bytes: 150 * 1024,
      alive_bytes: 1000 * 1024,
      gzip_bytes: 250 * 1024,
      active_bytes: 1500 * 1024,
      cpu_seconds: 7200,
      cpu_seconds_excluding_baseline: 3600,
      peak_rss_bytes: 6 * 2 ** 30,
    },
  },
});
const cpu = "?tab=pareto&size=cpu";
const point = (page: Page, id: string) =>
  page.locator(`[data-pareto-id="${id}"]`);
const open = async (page: Page, query = "?tab=pareto", data = sizes()) => {
  await routeCatalogue(page);
  await page.route("**/sizes.json", (route) => route.fulfill({ json: data }));
  await page.goto(`/${query}`);
};

test("Pareto is a tab between the leaderboard and milestones, not the landing view", async ({
  page,
}) => {
  await open(page, "");
  const nav = page.getByRole("navigation", { name: "Research views" });
  await expect(nav.getByRole("link", { name: "Timeline" })).toHaveAttribute(
    "aria-current",
    "page",
  );
  await expect(page.locator(".pareto-panel")).toHaveCount(0);
  await nav.getByRole("link", { name: "Pareto", exact: true }).click();
  expect(new URL(page.url()).searchParams.get("tab")).toBe("pareto");
  await expect(
    page.getByRole("region", { name: "Bound against proof size" }),
  ).toBeVisible();
  await expect(
    page.locator(".chart-panel[aria-label='Bound progress']"),
  ).toHaveCount(0);
  await expect(page.getByRole("list", { name: "Contributions" })).toBeVisible();
});

test("every verified result is plotted and the front is marked", async ({
  page,
}) => {
  await open(page, cpu);
  await expect(page.locator(".pareto-measure select")).toHaveValue("cpu");
  // The pending and historical fixtures are not verified results.
  await expect(page.locator("[data-pareto-id]")).toHaveCount(3);
  await expect(page.locator('[data-pareto-id][data-front="true"]')).toHaveCount(
    2,
  );
  await expect(point(page, "fixture-improvement")).toHaveAttribute(
    "data-front",
    "false",
  );
  await expect(point(page, "fixture-newest")).toHaveAttribute(
    "data-front",
    "true",
  );
  await expect(page.locator(".pareto-front")).toHaveAttribute(
    "d",
    /^M [\d.]+ [\d.]+ H /,
  );
  expect(
    await page.locator('.chart [data-axis="size"]').allTextContents(),
  ).toContain("1 h");
  await expect(page.locator(".pareto-panel .chart-note")).toContainText(
    "Lean 4.34.1 on Example CPU, 4 cores",
  );
  // Weaker bounds are higher and larger proofs further right.
  const box = async (id: string) =>
    (await point(page, id).locator("circle").nth(2).boundingBox())!;
  const [baseline, improvement, newest] = [
    await box("fixture-baseline"),
    await box("fixture-improvement"),
    await box("fixture-newest"),
  ];
  expect(improvement.x).toBeGreaterThan(newest.x);
  expect(improvement.y).toBeLessThan(newest.y);
  expect(newest.x).toBeGreaterThan(baseline.x);
  expect(newest.y).toBeGreaterThan(baseline.y);
});

test("focusing a result explains its bound, size and what dominates it", async ({
  page,
}) => {
  await open(page, cpu);
  await point(page, "fixture-improvement").focus();
  const tooltip = page.locator(".chart-tooltip");
  await expect(tooltip).toContainText("Example researcher · Improved bound");
  await expect(tooltip).toContainText("θ = 8749/10000 · cpu time 3 h");
  await expect(tooltip).toContainText(
    "Dominated by Example team · Newest improvement",
  );
  await point(page, "fixture-newest").focus();
  await expect(tooltip).toContainText("On the Pareto front");
  await point(page, "fixture-newest").blur();
  await expect(tooltip).toHaveCount(0);
});

test("arrow keys move between results in order of size", async ({ page }) => {
  await open(page);
  await point(page, "fixture-baseline").focus();
  await page.keyboard.press("ArrowRight");
  await expect(point(page, "fixture-newest")).toBeFocused();
  await page.keyboard.press("ArrowRight");
  await expect(point(page, "fixture-improvement")).toBeFocused();
  await page.keyboard.press("ArrowLeft");
  await expect(point(page, "fixture-newest")).toBeFocused();
});

test("results that overlap are reached by stepping through them", async ({
  page,
}) => {
  // A twin a hair larger and weaker than the newest result lands under it.
  const data = catalogue();
  data.records.push(
    record({
      id: "fixture-twin",
      title: "Example team · Twin result",
      authors: [{ name: "Example team" }],
      theta: { numerator: "874891", denominator: "1000000" },
      timeline_at: "2030-10-09T06:00:00Z",
      first_verified_at: "2030-10-11T13:00:00Z",
      certificate_url: "certificates/fixture-twin.json",
    }),
  );
  const withTwin = sizes();
  Object.assign(withTwin.entries, {
    "fixture-twin": {
      ...withTwin.entries["fixture-newest"],
      gzip_bytes: 251 * 1024,
    },
  });
  await routeCatalogue(page, data);
  await page.route("**/sizes.json", (route) =>
    route.fulfill({ json: withTwin }),
  );
  await page.goto("/?tab=pareto&size=gzip");
  await expect(page.locator("[data-pareto-id]")).toHaveCount(4);
  await point(page, "fixture-newest").hover();
  await expect(page.locator(".chart-tooltip")).toContainText(
    "2 results overlap here",
  );
  await point(page, "fixture-newest").click();
  await expect(point(page, "fixture-newest")).toHaveAttribute(
    "aria-pressed",
    "true",
  );
  await point(page, "fixture-newest").click();
  await expect(point(page, "fixture-twin")).toHaveAttribute(
    "aria-pressed",
    "true",
  );
  await expect(
    page.locator("#entry-fixture-twin .entry-details"),
  ).toBeVisible();
  await point(page, "fixture-newest").click();
  await expect(point(page, "fixture-newest")).toHaveAttribute(
    "aria-pressed",
    "true",
  );
  // A result with nothing under it is selected as before.
  await point(page, "fixture-baseline").click();
  await expect(point(page, "fixture-baseline")).toHaveAttribute(
    "aria-pressed",
    "true",
  );
});

test("the proof is sized by its alive code unless another measure is asked for", async ({
  page,
}) => {
  await open(page);
  await expect(page.locator(".pareto-measure select")).toHaveValue("alive");
  await expect(page.locator(".pareto-note")).toContainText(
    "Candidate.bound depends on",
  );
  await expect(page.locator("[data-pareto-id]")).toHaveCount(3);
  await expect(page.locator(".pareto-chart")).toContainText(
    "Alive code, gzipped · log scale",
  );
  // The size axis is logarithmic: round numbers of KiB, not evenly spaced values.
  const ticks = await page
    .locator('.chart [data-axis="size"]')
    .allTextContents();
  expect(ticks.length).toBeGreaterThanOrEqual(3);
  expect(ticks.every((tick) => /^\d+(\.\d)? KiB$/.test(tick))).toBe(true);
  // A source measure does not depend on the machine that compiled anything.
  await expect(page.locator(".pareto-panel .chart-note")).toHaveCount(0);
  await expect(page.locator('[data-pareto-id][data-front="true"]')).toHaveCount(
    2,
  );
  await expect(point(page, "fixture-improvement")).toHaveAttribute(
    "data-front",
    "false",
  );
  // Uncompressed, the stronger bounds are larger, so every result is on the front.
  await page.locator(".pareto-measure select").selectOption("alive-raw");
  await expect(page.locator('[data-pareto-id][data-front="true"]')).toHaveCount(
    3,
  );
  await page.locator(".pareto-table summary").click();
  await expect(page.locator(".pareto-table tbody tr").nth(0)).toContainText(
    "600 KiB",
  );
});

test("neither the number of modules nor of lines is a measure of a proof", async ({
  page,
}) => {
  await open(page);
  const options = await page
    .locator(".pareto-measure option")
    .evaluateAll((all) => all.map((o) => (o as HTMLOptionElement).value));
  expect(options).toEqual([
    "alive",
    "alive-raw",
    "cpu",
    "cpu-own",
    "gzip",
    "memory",
  ]);
  // An old link to one of them opens the default instead.
  await open(page, "?tab=pareto&size=modules");
  await expect(page.locator(".pareto-measure select")).toHaveValue("alive");
});

test("the size measure can be changed and survives reload and sharing", async ({
  page,
  context,
}) => {
  await open(page);
  await page.locator(".pareto-measure select").selectOption("gzip");
  expect(new URL(page.url()).searchParams.get("size")).toBe("gzip");
  await expect(page.locator('[data-pareto-id][data-front="true"]')).toHaveCount(
    2,
  );
  await expect(page.locator(".pareto-note")).toContainText(
    "Every file the proof imports",
  );
  await page.reload();
  await expect(page.locator(".pareto-measure select")).toHaveValue("gzip");
  const shared = await context.newPage();
  await open(shared, "?tab=pareto&size=memory");
  await expect(shared.locator(".pareto-measure select")).toHaveValue("memory");
  await expect(
    shared.locator('.chart [data-axis="size"]').first(),
  ).toContainText("GiB");
  await open(shared, "?tab=pareto&size=unknown");
  await expect(shared.locator(".pareto-measure select")).toHaveValue("alive");
  await shared.close();
});

test("the reachable modules, gzipped, are a measure of their own", async ({
  page,
}) => {
  await open(page, "?tab=pareto&size=gzip");
  await expect(page.locator(".pareto-measure select")).toHaveValue("gzip");
  await expect(page.locator("[data-pareto-id]")).toHaveCount(3);
  await expect(
    page.locator('.chart [data-axis="size"]').filter({ hasText: "200 KiB" }),
  ).toHaveCount(1);
  await expect(page.locator(".pareto-chart")).toContainText(
    "Reachable modules, gzipped · log scale",
  );
});

test("selecting a result opens its leaderboard entry", async ({ page }) => {
  await open(page);
  await point(page, "fixture-improvement").click();
  await expect(point(page, "fixture-improvement")).toHaveAttribute(
    "aria-pressed",
    "true",
  );
  await expect(
    page.locator("#entry-fixture-improvement .entry-details"),
  ).toBeVisible();
});

test("the table view lists the same results and what dominates them", async ({
  page,
}) => {
  await open(page, cpu);
  const table = page.locator(".pareto-table");
  await table.locator("summary").click();
  const rows = table.locator("tbody tr");
  await expect(rows).toHaveCount(3);
  await expect(rows.nth(0)).toContainText("Example author · Initial bound");
  await expect(rows.nth(0)).toContainText("1 h");
  await expect(rows.nth(0)).toContainText("Yes");
  await expect(rows.nth(2)).toContainText(
    "Example researcher · Improved bound",
  );
  await expect(rows.nth(2)).toContainText(
    "No, dominated by Example team · Newest improvement",
  );
  await rows.nth(2).getByRole("button").click();
  await expect(
    page.locator("#entry-fixture-improvement .entry-details"),
  ).toBeVisible();
});

test("measures nobody has measured yet are offered but not selectable, and alive code stands in", async ({
  page,
}) => {
  const sourceOnly = sizes();
  for (const entry of Object.values(sourceOnly.entries))
    for (const key of [
      "cpu_seconds",
      "cpu_seconds_excluding_baseline",
      "peak_rss_bytes",
    ])
      delete (entry as Record<string, number>)[key];
  await open(page, "?tab=pareto", sourceOnly);
  await expect(page.locator(".pareto-measure select")).toHaveValue("alive");
  await expect(page.locator("[data-pareto-id]")).toHaveCount(3);
  const cpuOption = page.locator(".pareto-measure option[value='cpu']");
  await expect(cpuOption).toHaveJSProperty("disabled", true);
  await expect(cpuOption).toContainText("not measured yet");
});

test("the reachable modules stand in until alive code and compile cost are known", async ({
  page,
}) => {
  const modulesOnly = sizes();
  for (const entry of Object.values(modulesOnly.entries))
    for (const key of [
      "cpu_seconds",
      "cpu_seconds_excluding_baseline",
      "peak_rss_bytes",
      "alive_gzip_bytes",
      "alive_bytes",
    ])
      delete (entry as Record<string, number>)[key];
  await open(page, "?tab=pareto", modulesOnly);
  await expect(page.locator(".pareto-measure select")).toHaveValue("gzip");
  await expect(page.locator("[data-pareto-id]")).toHaveCount(3);
  await expect(
    page.locator(".pareto-measure option[value='alive']"),
  ).toContainText("not measured yet");
});

test("results without a measurement are listed as missing, not plotted", async ({
  page,
}) => {
  const partial = sizes();
  delete (partial.entries as Record<string, unknown>)["fixture-newest"];
  await open(page, "?tab=pareto", partial);
  await expect(page.locator("[data-pareto-id]")).toHaveCount(2);
  await expect(page.locator(".pareto-panel .chart-note").first()).toContainText(
    "1 verified result has no alive code measurement yet and is not plotted.",
  );
});

test("the rest of the site works when proof sizes cannot be loaded", async ({
  page,
}) => {
  const failures: string[] = [];
  page.on("pageerror", (error) => failures.push(error.message));
  await routeCatalogue(page);
  await page.route("**/sizes.json", (route) => route.fulfill({ status: 404 }));
  await page.goto("/?tab=pareto");
  await expect(page.locator("[data-pareto-id]")).toHaveCount(0);
  await expect(page.locator(".pareto-chart")).toContainText(
    "No results have this measurement yet.",
  );
  await expect(page.locator(".notice.error")).toHaveCount(0);
  await page
    .getByRole("navigation", { name: "Research views" })
    .getByRole("link", { name: "Timeline" })
    .click();
  await expect(page.locator(".verified-frontier")).toHaveAttribute("d", /^M/);
  expect(failures).toEqual([]);
});
