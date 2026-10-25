import { test, expect, type Page } from "@playwright/test";
import { routeCatalogue } from "./catalogue-fixture";

// The fixture bounds are 7/8 > 8749/10000 > 87489/100000. By compile CPU the
// newest result is both stronger and cheaper than the improvement, so only the
// baseline and the newest result are on the front. By lines of Lean every
// stronger bound costs more, so all three are.
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
      modules: 100,
      lines: 10000,
      cpu_seconds: 3600,
      cpu_seconds_excluding_baseline: 0.1,
      peak_rss_bytes: 4 * 2 ** 30,
    },
    "fixture-improvement": {
      modules: 150,
      lines: 15000,
      cpu_seconds: 10800,
      cpu_seconds_excluding_baseline: 7200,
      peak_rss_bytes: 5 * 2 ** 30,
    },
    "fixture-newest": {
      modules: 140,
      lines: 20000,
      cpu_seconds: 7200,
      cpu_seconds_excluding_baseline: 3600,
      peak_rss_bytes: 6 * 2 ** 30,
    },
  },
});
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
  await expect(page.getByRole("region", { name: "Bound against proof size" })).toBeVisible();
  await expect(page.locator(".chart-panel[aria-label='Bound progress']")).toHaveCount(0);
  await expect(page.getByRole("list", { name: "Contributions" })).toBeVisible();
});

test("every verified result is plotted and the front is marked", async ({
  page,
}) => {
  await open(page);
  await expect(page.locator(".pareto-measure select")).toHaveValue("cpu");
  // The pending and historical fixtures are not verified results.
  await expect(page.locator("[data-pareto-id]")).toHaveCount(3);
  await expect(page.locator('[data-pareto-id][data-front="true"]')).toHaveCount(2);
  await expect(point(page, "fixture-improvement")).toHaveAttribute("data-front", "false");
  await expect(point(page, "fixture-newest")).toHaveAttribute("data-front", "true");
  await expect(page.locator(".pareto-front")).toHaveAttribute("d", /^M [\d.]+ [\d.]+ H /);
  expect(await page.locator('.chart [data-axis="size"]').allTextContents()).toContain("1 h");
  await expect(page.locator(".pareto-panel .chart-note")).toContainText(
    "Lean 4.34.1 on Example CPU, 4 cores",
  );
  // Weaker bounds are higher and larger proofs further right.
  const box = async (id: string) => (await point(page, id).locator("circle").nth(2).boundingBox())!;
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
  await open(page);
  await point(page, "fixture-improvement").focus();
  const tooltip = page.locator(".chart-tooltip");
  await expect(tooltip).toContainText("Example researcher · Improved bound");
  await expect(tooltip).toContainText("θ = 8749/10000 · cpu time 3 h");
  await expect(tooltip).toContainText("Dominated by Example team · Newest improvement");
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

test("the size measure can be changed and survives reload and sharing", async ({
  page,
  context,
}) => {
  await open(page);
  await page.locator(".pareto-measure select").selectOption("lines");
  expect(new URL(page.url()).searchParams.get("size")).toBe("lines");
  await expect(page.locator('[data-pareto-id][data-front="true"]')).toHaveCount(3);
  await expect(page.locator(".pareto-note")).toContainText("Lines of source");
  await page.reload();
  await expect(page.locator(".pareto-measure select")).toHaveValue("lines");
  const shared = await context.newPage();
  await open(shared, "?tab=pareto&size=memory");
  await expect(shared.locator(".pareto-measure select")).toHaveValue("memory");
  await expect(shared.locator('.chart [data-axis="size"]').first()).toContainText("GiB");
  await open(shared, "?tab=pareto&size=unknown");
  await expect(shared.locator(".pareto-measure select")).toHaveValue("cpu");
  await shared.close();
});

test("selecting a result opens its leaderboard entry", async ({ page }) => {
  await open(page);
  await point(page, "fixture-improvement").click();
  await expect(point(page, "fixture-improvement")).toHaveAttribute("aria-pressed", "true");
  await expect(page.locator("#entry-fixture-improvement .entry-details")).toBeVisible();
});

test("the table view lists the same results and what dominates them", async ({
  page,
}) => {
  await open(page);
  const table = page.locator(".pareto-table");
  await table.locator("summary").click();
  const rows = table.locator("tbody tr");
  await expect(rows).toHaveCount(3);
  await expect(rows.nth(0)).toContainText("Example author · Initial bound");
  await expect(rows.nth(0)).toContainText("1 h");
  await expect(rows.nth(0)).toContainText("Yes");
  await expect(rows.nth(2)).toContainText("Example researcher · Improved bound");
  await expect(rows.nth(2)).toContainText("No, dominated by Example team · Newest improvement");
  await rows.nth(2).getByRole("button").click();
  await expect(page.locator("#entry-fixture-improvement .entry-details")).toBeVisible();
});

test("measures nobody has measured yet are offered but not selectable, and counts stand in", async ({
  page,
}) => {
  const sourceOnly = sizes();
  for (const entry of Object.values(sourceOnly.entries))
    for (const key of ["cpu_seconds", "cpu_seconds_excluding_baseline", "peak_rss_bytes"])
      delete (entry as Record<string, number>)[key];
  await open(page, "?tab=pareto", sourceOnly);
  await expect(page.locator(".pareto-measure select")).toHaveValue("modules");
  await expect(page.locator("[data-pareto-id]")).toHaveCount(3);
  const cpu = page.locator(".pareto-measure option[value='cpu']");
  await expect(cpu).toHaveJSProperty("disabled", true);
  await expect(cpu).toContainText("not measured yet");
});

test("results without a measurement are listed as missing, not plotted", async ({
  page,
}) => {
  const partial = sizes();
  delete (partial.entries as Record<string, unknown>)["fixture-newest"];
  await open(page, "?tab=pareto", partial);
  await expect(page.locator("[data-pareto-id]")).toHaveCount(2);
  await expect(page.locator(".pareto-panel .chart-note").first()).toContainText(
    "1 verified result has no cpu time measurement yet and is not plotted.",
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
  await expect(page.locator(".pareto-chart")).toContainText("No results have this measurement yet.");
  await expect(page.locator(".notice.error")).toHaveCount(0);
  await page
    .getByRole("navigation", { name: "Research views" })
    .getByRole("link", { name: "Timeline" })
    .click();
  await expect(page.locator(".verified-frontier")).toHaveAttribute("d", /^M/);
  expect(failures).toEqual([]);
});
