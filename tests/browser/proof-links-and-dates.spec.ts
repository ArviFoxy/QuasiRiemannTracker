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
      await expect(badge).toHaveAttribute("href", /\/Solution\.lean$/);
      const href = (await badge.getAttribute("href"))!;
      const path = new URL(href).pathname.split("/public/")[1];
      const response = await request.get(`/${path}`);
      expect(response.ok()).toBe(true);
      const source = await response.text();
      expect(source).toMatch(/\btheorem\b/);
      expect(source).not.toMatch(/\bsorry\b/);
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

test("flat-layout solution references beat challenge templates; unknown layouts are not proof links", async ({
  page,
}) => {
  // Isolated response fixtures model the flat layout used by Akash's snapshot.
  const flat = {
    ...catalogue.records[0],
    id: "test-flat-layout",
    title: "Test fixture · flat layout",
    timeline_at: undefined,
    date_label: undefined,
    references: [
      {
        label: "Exact checked statements",
        url: "proofs/test-flat/Challenge.lean",
      },
      { label: "Solution wrapper", url: "proofs/test-flat/Solution.lean" },
    ],
  };
  const unknown = {
    ...flat,
    id: "test-unknown-layout",
    title: "Test fixture · unknown layout",
    references: [flat.references[0]],
  };
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({ json: { schema_version: 1, records: [flat, unknown] } }),
  );
  await page.route("**/registry.json", (route) =>
    route.fulfill({
      json: { schema_version: 1, records: [], events: [], active_ids: [] },
    }),
  );
  await page.goto("/");
  const row = page.locator("tbody tr").filter({
    has: page.getByRole("button", { name: flat.title, exact: true }),
  });
  await expect(row.locator(".verification-badge")).toHaveAttribute(
    "href",
    "https://github.com/GTimG/QuasiRiemannTracker/blob/main/public/proofs/test-flat/Solution.lean",
  );
  await expect(row.locator('td[data-label="Date"] small')).toHaveText(
    "First verified",
  );
  await expect(row.locator("time")).toHaveAttribute(
    "datetime",
    flat.first_verified_at,
  );
  const unknownRow = page.locator("tbody tr").filter({
    has: page.getByRole("button", { name: unknown.title, exact: true }),
  });
  await expect(unknownRow).toBeVisible();
  await expect(unknownRow.locator(".verification-badge")).not.toHaveAttribute(
    "href",
  );
});
