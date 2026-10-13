import { test, expect } from "@playwright/test";
import { record, routeCatalogue } from "./catalogue-fixture";
import { withSubmissionTimeline } from "../../core/catalogue.mjs";

test("an earlier submission is a record even when the stronger proof verifies first", async ({
  page,
}, info) => {
  // Synthetic data is confined to this routed browser fixture.
  const early = withSubmissionTimeline(
    record({
      id: "fixture-early-pr",
      title: "Example earlier submission",
      pr: 41,
      theta: { numerator: "8748673", denominator: "10000000" },
      submitted_at: "2030-10-12T15:53:59Z",
      first_verified_at: "2030-10-13T00:00:27Z",
      merged_at: "2030-10-13T02:00:00Z",
    }),
  );
  const stronger = withSubmissionTimeline(
    record({
      id: "fixture-stronger-pr",
      title: "Example later submission",
      pr: 42,
      theta: { numerator: "874861", denominator: "1000000" },
      submitted_at: "2030-10-12T16:56:38Z",
      first_verified_at: "2030-10-13T00:00:00Z",
      merged_at: "2030-10-13T02:01:00Z",
    }),
  );
  await routeCatalogue(page, {
    schema_version: 1,
    records: [record(), stronger, early],
  });
  await page.goto("/");
  const firstDot = page.locator('[data-dot][data-id="fixture-early-pr"]');
  const secondDot = page.locator('[data-dot][data-id="fixture-stronger-pr"]');
  await expect(firstDot).toHaveAttribute(
    "data-time",
    String(Date.parse(early.submitted_at)),
  );
  await expect(secondDot).toHaveAttribute(
    "data-time",
    String(Date.parse(stronger.submitted_at)),
  );
  for (const dot of [firstDot, secondDot])
    await expect(dot.locator("circle[stroke]")).toHaveAttribute(
      "fill",
      "#1d5d74",
    );
  expect(
    Number(await firstDot.locator("circle[stroke]").getAttribute("cx")),
  ).toBeLessThan(
    Number(await secondDot.locator("circle[stroke]").getAttribute("cx")),
  );
  await page.getByRole("button", { name: early.title, exact: true }).click();
  const details = page.locator(".proof-detail");
  await expect(details).toContainText("PR submitted");
  await expect(details).toContainText("2030-10-12 15:53:59 UTC");
  await expect(details).toContainText("First verified here");
  await expect(details).toContainText("2030-10-13 00:00:27 UTC");
  await expect(details).toContainText("2030-10-13 02:00:00 UTC");
  expect(
    await page.evaluate(
      () => document.documentElement.scrollWidth <= window.innerWidth,
    ),
  ).toBeTruthy();
  await page.screenshot({
    path: `evidence/screenshots/${info.project.name}-submission-timeline.png`,
    fullPage: true,
  });
});
