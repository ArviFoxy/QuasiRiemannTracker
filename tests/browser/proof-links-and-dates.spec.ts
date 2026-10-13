import { test, expect } from "@playwright/test";
import { readFileSync } from "node:fs";

const catalogue = JSON.parse(
  readFileSync(
    new URL("../../catalogue/results.json", import.meta.url),
    "utf8",
  ),
);

test("verified proof badges open solution sources and contribution dates retain their meaning", async ({
  page,
  request,
}) => {
  await page.goto("/");
  await expect(
    page.getByRole("button", { name: "Date", exact: true }),
  ).toBeVisible();
  for (const record of catalogue.records) {
    const row = page.locator("tbody tr").filter({
      has: page.getByRole("button", { name: record.title, exact: true }),
    });
    const badge = row.locator(".verification-badge");
    if (record.status === "framework-verified") {
      await expect(badge).toHaveAttribute("href", /\.lean$/);
      const href = (await badge.getAttribute("href"))!;
      expect(href).toBe(record.solution_url);
      expect(new URL(href).pathname).toMatch(
        /\/blob\/[a-f0-9]{40}\/.+\.lean$/,
      );
    } else if (record.status === "historical-baseline") {
      await expect(row.locator(".tag.historical")).toHaveText(
        "Historical baseline",
      );
    } else {
      expect(record.status).toBe("verification-pending");
      await expect(badge).toHaveClass(/\bamber\b/);
      await expect(badge.locator(".sr-only")).toHaveText(
        "Verification pending",
      );
    }
    const dateCell = row.locator('td[data-label="Date"]');
    await expect(dateCell.locator("time")).toHaveAttribute(
      "datetime",
      record.date_precision === "year"
        ? record.timeline_at.slice(0, 4)
        : record.timeline_at,
    );
    await expect(dateCell.locator("small")).toHaveText(record.date_label);
  }
});
