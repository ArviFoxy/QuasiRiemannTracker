import { test, expect } from "@playwright/test";
import { routeCatalogue } from "./catalogue-fixture";

test("milestone range preserves points and the leaderboard fit restores the initial view", async ({
  page,
}) => {
  await routeCatalogue(page);
  await page.goto("/");
  const chart = page.locator(".chart");
  await expect(chart.locator("[data-dot]").first()).toBeAttached();
  const initialBounds = await chart
    .locator('[data-axis="bound"]')
    .allTextContents();
  const initialDates = await chart
    .locator('[data-axis="date"]')
    .allTextContents();
  const count = await chart.locator("[data-dot]").count();
  await page.getByRole("button", { name: "Fit ½–1", exact: true }).click();
  for (const id of ["one", "thirteen-fifteenths", "three-quarters", "half"]) {
    const line = chart.locator(`[data-milestone="${id}"]`);
    const y = Number(await line.getAttribute("y1"));
    expect(y).toBeGreaterThan(35);
    expect(y).toBeLessThan(295);
    expect(await line.getAttribute("y2")).toBe(String(y));
    expect(await line.getAttribute("stroke-dasharray")).toBe(
      ["one", "half"].includes(id) ? null : "7 5",
    );
  }
  const bounds = await chart.locator('[data-axis="bound"]').allTextContents();
  expect(Number(bounds[0].replace("…", ""))).toBeGreaterThan(1);
  expect(Number(bounds.at(-1)!.replace("…", ""))).toBeLessThan(0.5);
  await expect(chart.locator("[data-dot]")).toHaveCount(count);
  await chart.focus();
  await chart.press("+");
  await chart.press("ArrowDown");
  await page.getByRole("button", { name: "Fit ½–1", exact: true }).click();
  await expect(chart.locator('[data-axis="bound"]')).toHaveText(bounds);
  await page
    .getByRole("button", { name: "Fit leaderboard", exact: true })
    .click();
  await expect(chart.locator('[data-axis="bound"]')).toHaveText(initialBounds);
  await expect(chart.locator('[data-axis="date"]')).toHaveText(initialDates);
  await page.getByRole("button", { name: "Fit ½–1", exact: true }).click();
  await chart.focus();
  await chart.press("Home");
  await expect(chart.locator('[data-axis="bound"]')).toHaveText(initialBounds);
});

test("milestones sit between leaderboard and protocol and fit narrow screens", async ({
  page,
}) => {
  await routeCatalogue(page);
  await page.goto("/");
  const nav = page.getByRole("navigation", { name: "Research views" });
  await expect(nav.getByRole("button")).toHaveText([
    "Timeline",
    /Leaderboard/,
    "Milestones",
    "Protocol",
  ]);
  await nav.getByRole("button", { name: "Milestones", exact: true }).click();
  await expect(
    page.getByRole("heading", { name: "From one to the critical line" }),
  ).toBeVisible();
  await expect(page.locator(".milestone-list > li")).toHaveCount(4);
  await expect(page.locator(".milestone-source")).toHaveCount(4);
  await expect(page.locator(".milestones")).toContainText("Dirichlet GRH");
  await expect(page.locator(".milestones")).toContainText(
    "Intermediate milestone",
  );
  for (const width of [320, 390, 768]) {
    await page.setViewportSize({ width, height: 844 });
    expect(
      await page.evaluate(
        () => document.documentElement.scrollWidth <= innerWidth,
      ),
    ).toBe(true);
    await expect(
      nav.getByRole("button", { name: "Protocol", exact: true }),
    ).toBeInViewport();
  }
});
