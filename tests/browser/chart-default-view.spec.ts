import { test, expect } from "@playwright/test";
import { readFileSync } from "node:fs";
import { cmp, decimal } from "../../core/rational.mjs";

const catalogue = JSON.parse(readFileSync("catalogue/results.json", "utf8"));
const verified = catalogue.records.filter(
  (record: { status: string }) => record.status === "framework-verified",
);
const best = [...verified].sort((a, b) => cmp(a.theta, b.theta))[0];

test("default chart fits the verified frontier below one and restores it from full history", async ({
  page,
}) => {
  const source = verified[0];
  const historical = {
    ...source,
    id: "historical-1922-fixture",
    title: "Historical boundary from 1922",
    status: "historical-baseline",
    theta: { numerator: "1", denominator: "1" },
    timeline_at: "1922-01-01T00:00:00Z",
    date_precision: "year",
    date_label: "Publication year",
    first_verified_at: "",
    receipt_url: "",
    log_url: "",
    entrypoint: { module: "", declaration: "" },
    builds_on: [],
    references: [
      { label: "Publication", url: "https://example.com/historical" },
    ],
  };
  const weaker = {
    ...source,
    id: "verified-weaker-fixture",
    title: "Later verified weaker bound",
    theta: { numerator: "29", denominator: "33" },
    timeline_at: "2034-01-01T00:00:00Z",
    first_verified_at: "2034-01-01T00:00:00Z",
    builds_on: [],
  };
  const pending = {
    ...source,
    id: "pending-better-fixture",
    title: "Pending stronger claim",
    status: "verification-pending",
    theta: { numerator: "1", denominator: "2" },
    timeline_at: "1859-01-01T00:00:00Z",
    first_verified_at: "",
    builds_on: [],
  };
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({
      json: {
        ...catalogue,
        records: [...catalogue.records, historical, weaker, pending],
      },
    }),
  );
  await page.goto("/");

  const chart = page.locator(".chart");
  const bestView = page.getByRole("button", {
    name: "Best verified",
    exact: true,
  });
  const fullView = page.getByRole("button", {
    name: "Full history",
    exact: true,
  });
  const summary = page.getByRole("button", {
    name: "View best verified proof",
  });
  const boundTicks = chart.locator('[data-axis="bound"]');
  const dateTicks = chart.locator('[data-axis="date"]');

  await expect(bestView).toHaveAttribute("aria-pressed", "true");
  await expect(chart.locator(`[data-id="${best.id}"]`)).toBeVisible();
  await expect(
    chart.locator('[data-id="historical-1922-fixture"]'),
  ).toHaveCount(0);
  await expect(
    chart.locator('[data-id="verified-weaker-fixture"]'),
  ).toHaveCount(0);
  await expect(chart.locator('[data-id="pending-better-fixture"]')).toHaveCount(
    0,
  );
  const initialBounds = await boundTicks.allTextContents();
  expect(initialBounds).toHaveLength(5);
  for (const text of initialBounds) {
    const theta = Number(text.replace("…", ""));
    expect(theta).toBeGreaterThan(0.874);
    expect(theta).toBeLessThan(0.876);
  }
  const initialDates = await dateTicks.allTextContents();
  expect(initialDates.every((date) => date.includes("Oct"))).toBe(true);
  const summaryText = await summary.innerText();
  expect(summaryText).toContain(decimal(best.theta, 8).replace("…", ""));
  for (const result of [historical, weaker, pending]) {
    await expect(
      page.getByRole("button", { name: result.title, exact: true }),
    ).toBeVisible();
  }

  await fullView.click();
  await expect(fullView).toHaveAttribute("aria-pressed", "true");
  await expect(
    chart.locator('[data-id="historical-1922-fixture"]'),
  ).toBeVisible();
  await expect(
    chart.locator('[data-id="verified-weaker-fixture"]'),
  ).toBeVisible();
  await expect(chart.locator('[data-id="pending-better-fixture"]')).toHaveCount(
    0,
  );
  const years = (await dateTicks.allTextContents()).map(Number);
  expect(Math.min(...years)).toBeLessThan(1922);
  expect(Math.max(...years)).toBeGreaterThan(2034);
  expect(await summary.innerText()).toBe(summaryText);

  await bestView.click();
  await expect(boundTicks).toHaveText(initialBounds);
  await expect(dateTicks).toHaveText(initialDates);
  await fullView.click();
  await chart.focus();
  await chart.press("Home");
  await expect(bestView).toHaveAttribute("aria-pressed", "true");
  await expect(boundTicks).toHaveText(initialBounds);
  await expect(dateTicks).toHaveText(initialDates);
  await expect(
    chart.locator('[data-id="verified-weaker-fixture"]'),
  ).toHaveCount(0);
  expect(await summary.innerText()).toBe(summaryText);
});
