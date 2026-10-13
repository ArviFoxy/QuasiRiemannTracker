import type { Page } from "@playwright/test";
import { catalogue } from "../fixtures/catalogue.mjs";

export {
  catalogue,
  record,
  historicalRecord,
  algebraicRecord,
} from "../fixtures/catalogue.mjs";

export async function routeCatalogue(page: Page, data = catalogue()) {
  await page.route("**/catalogue.json", (route) =>
    route.fulfill({ json: data }),
  );
}
