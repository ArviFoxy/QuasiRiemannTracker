import { BASELINE, cmp, reduced, sub } from "./rational.mjs";

// Smaller is better on both axes: a bound closer to 1/2 and a smaller proof.
// A point is dominated when another is at least as good on both and strictly
// better on one. Points that are equal on both do not dominate each other.
// Each point is { id, theta: { numerator, denominator }, size: positive number }.
export function paretoFront(points) {
  const order = [...points].sort(
    (a, b) => a.size - b.size || cmp(a.theta, b.theta) || (a.id < b.id ? -1 : 1),
  );
  const front = [];
  let best = null;
  for (let start = 0; start < order.length; ) {
    let end = start;
    while (end < order.length && order[end].size === order[start].size) end++;
    // Within one size only the strongest bound survives, and only if it beats
    // every bound that is already available at a smaller size.
    const lowest = order[start].theta;
    if (best === null || cmp(lowest, best) < 0) {
      front.push(
        ...order.slice(start, end).filter((p) => cmp(p.theta, lowest) === 0),
      );
      best = lowest;
    }
    start = end;
  }
  const onFront = new Set(front.map((p) => p.id));
  const dominators = new Map(
    points
      .filter((p) => !onFront.has(p.id))
      .map((p) => [
        p.id,
        front.filter((q) => q.size <= p.size && cmp(q.theta, p.theta) <= 0),
      ]),
  );
  return { front, onFront, dominators };
}

// The weakest bound the chart zooms to: results that do not beat the OpenAI
// baseline (7/8) are drawn at the top edge instead of flattening the rest.
export const inScale = (point) => cmp(point.theta, BASELINE) <= 0;

// Exact bounds of the vertical axis, with room around the plotted extremes.
export function thetaDomain(thetas) {
  let low = thetas[0],
    high = thetas[0];
  for (const t of thetas) {
    if (cmp(t, low) < 0) low = t;
    if (cmp(t, high) > 0) high = t;
  }
  let span = sub(high, low);
  if (span.numerator === "0")
    span = reduced(BigInt(high.numerator), BigInt(high.denominator) * 1000n);
  const pad = (n, d) =>
    reduced(BigInt(span.numerator) * n, BigInt(span.denominator) * d);
  const above = pad(1n, 10n);
  return {
    low: sub(low, pad(3n, 25n)),
    high: sub(high, { ...above, numerator: String(-BigInt(above.numerator)) }),
  };
}

// Tick values of the form m * 10^k, for the smallest mantissa set that gives
// a readable count. Works on any positive range; the log axis uses these.
export function logTicks(min, max, scale = 1) {
  const lo = min / scale,
    hi = max / scale;
  const sets = [[1], [1, 3], [1, 2, 5], [1, 1.5, 2, 3, 5, 7], [1, 1.2, 1.5, 2, 2.5, 3, 4, 5, 6, 8]];
  let ticks = [];
  for (const mantissas of sets) {
    ticks = [];
    for (let k = Math.floor(Math.log10(lo)) - 1; k <= Math.ceil(Math.log10(hi)); k++)
      for (const m of mantissas) {
        const v = m * 10 ** k;
        if (v >= lo * (1 - 1e-9) && v <= hi * (1 + 1e-9)) ticks.push(v);
      }
    if (ticks.length >= 4) break;
  }
  return ticks.map((v) => v * scale);
}

// Evenly spaced tick values at multiples of 1, 2 or 5 times a power of ten.
export function linearTicks(min, max, target = 5) {
  const rough = (max - min) / target,
    power = 10 ** Math.floor(Math.log10(rough));
  // The step closest to the target spacing, comparing ratios.
  const step = Number(
    [1, 2, 5, 10]
      .map((m) => m * power)
      .reduce((a, b) =>
        Math.abs(Math.log(b / rough)) < Math.abs(Math.log(a / rough)) ? b : a,
      )
      .toPrecision(12),
  );
  const ticks = [];
  for (let v = Math.ceil(min / step - 1e-9) * step; v <= max + step * 1e-9; v += step)
    ticks.push(Number(v.toPrecision(12)));
  return { ticks, step };
}
