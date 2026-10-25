import { BASELINE, cmp, reduced, sub } from "./rational.mjs";

// Smaller is better on both axes: a bound closer to 1/2 and a smaller proof.
// A point is dominated when another is at least as good on both and strictly
// better on one. Points that are equal on both do not dominate each other.
// Each point is { id, theta: { numerator, denominator }, size: positive number }.
export function paretoFront(points) {
  const order = [...points].sort(
    (a, b) =>
      a.size - b.size || cmp(a.theta, b.theta) || (a.id < b.id ? -1 : 1),
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

// Tick values for a log axis: round numbers in the unit they are printed in
// (200 KiB, 5 MiB, 2 h), using the fewest per decade that still gives four and
// none closer on screen than gap. Each unit is { size, max }: how many base
// units it is worth, and the largest count of it worth printing (59 minutes,
// but 900 KiB). position maps a value to its place on the axis.
export function logTicks(
  min,
  max,
  units,
  { position = Math.log, gap = 0 } = {},
) {
  const sets = [
    [1],
    [1, 3],
    [1, 2, 5],
    [1, 1.5, 2, 3, 5, 7],
    [1, 1.2, 1.5, 2, 2.5, 3, 4, 5, 6, 8],
  ];
  let kept = [];
  for (const mantissas of sets) {
    const ticks = [];
    for (const { size, max: limit } of units)
      for (let k = 0; 10 ** k <= limit; k++)
        for (const m of mantissas) {
          const count = m * 10 ** k,
            value = count * size;
          if (
            count <= limit &&
            value >= min * (1 - 1e-9) &&
            value <= max * (1 + 1e-9)
          )
            ticks.push(value);
        }
    ticks.sort((a, b) => a - b);
    kept = [];
    for (const t of ticks)
      if (
        !kept.length ||
        (t !== kept.at(-1) && position(t) - position(kept.at(-1)) >= gap)
      )
        kept.push(t);
    if (kept.length >= 4) break;
  }
  return kept;
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
  for (
    let v = Math.ceil(min / step - 1e-9) * step;
    v <= max + step * 1e-9;
    v += step
  )
    ticks.push(Number(v.toPrecision(12)));
  return { ticks, step };
}
