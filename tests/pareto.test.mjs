import test from "node:test";
import assert from "node:assert/strict";
import {
  inScale,
  linearTicks,
  logTicks,
  paretoFront,
  thetaDomain,
} from "../core/pareto.mjs";
import { cmp, rational, reduced } from "../core/rational.mjs";

const point = (id, numerator, denominator, size) => ({
  id,
  theta: reduced(BigInt(numerator), BigInt(denominator)),
  size,
});
const ids = (points) => points.map((p) => p.id);

test("the front keeps results that no other result beats on both axes", () => {
  const { front, onFront, dominators } = paretoFront([
    point("cheap", 7, 8, 100),
    point("middle", 3, 4, 300),
    point("late", 4, 5, 400),
    point("strong", 7, 10, 500),
  ]);
  assert.deepEqual(ids(front), ["cheap", "middle", "strong"]);
  assert.deepEqual([...onFront].sort(), ["cheap", "middle", "strong"]);
  assert.deepEqual([...dominators.keys()], ["late"]);
  // "cheap" is faster but weaker, so only "middle" beats it on both axes.
  assert.deepEqual(ids(dominators.get("late")), ["middle"]);
});

test("a stronger bound at the same size dominates, and equal results both stay", () => {
  const { front, dominators } = paretoFront([
    point("a", 7, 8, 100),
    point("b", 3, 4, 300),
    point("c", 7, 10, 300),
    point("d", 7, 10, 300),
  ]);
  assert.deepEqual(ids(front), ["a", "c", "d"]);
  assert.deepEqual(ids(dominators.get("b")), ["c", "d"]);
});

test("a larger proof with the same bound is dominated, a smaller one is not", () => {
  const { onFront } = paretoFront([
    point("small", 4, 5, 100),
    point("large", 4, 5, 200),
  ]);
  assert.deepEqual([...onFront], ["small"]);
});

test("the front does not depend on input order", () => {
  const points = [
    point("a", 87, 100, 100),
    point("b", 86, 100, 120),
    point("c", 88, 100, 90),
    point("d", 85, 100, 300),
    point("e", 86, 100, 110),
    point("f", 90, 100, 500),
  ];
  const expected = ids(paretoFront(points).front);
  for (let shift = 1; shift < points.length; shift++)
    assert.deepEqual(
      ids(
        paretoFront([...points.slice(shift), ...points.slice(0, shift)]).front,
      ),
      expected,
    );
  assert.deepEqual(expected, ["c", "a", "e", "d"]);
});

test("bounds that differ beyond float precision are ranked exactly", () => {
  const weaker = point(
    "weaker",
    "875000000000000000000000000001",
    "1000000000000000000000000000000",
    10,
  );
  const stronger = point(
    "stronger",
    "875000000000000000000000000000",
    "1000000000000000000000000000000",
    10,
  );
  assert.equal(
    Number(weaker.theta.numerator) / Number(weaker.theta.denominator),
    Number(stronger.theta.numerator) / Number(stronger.theta.denominator),
  );
  assert.deepEqual(ids(paretoFront([weaker, stronger]).front), ["stronger"]);
});

test("nothing to plot has an empty front", () => {
  const { front, onFront, dominators } = paretoFront([]);
  assert.deepEqual([front, [...onFront], [...dominators]], [[], [], []]);
});

test("only bounds at or below the OpenAI baseline are in scale", () => {
  assert.equal(inScale(point("a", 7, 8, 1)), true);
  assert.equal(inScale(point("b", 8749, 10000, 1)), true);
  assert.equal(inScale(point("c", 29, 33, 1)), false);
  assert.equal(inScale(point("d", 1, 1, 1)), false);
});

test("the vertical domain contains every bound with room around it", () => {
  const thetas = [
    rational("874773", "1000000"),
    rational("7", "8"),
    rational("87477299", "100000000"),
  ];
  const { low, high } = thetaDomain(thetas);
  for (const t of thetas) {
    assert.equal(cmp(low, t) < 0, true);
    assert.equal(cmp(high, t) > 0, true);
  }
  const equal = thetaDomain([rational("7", "8"), rational("7", "8")]);
  assert.equal(cmp(equal.low, equal.high) < 0, true);
  const single = thetaDomain([rational("7", "8")]);
  assert.equal(cmp(single.low, rational("7", "8")) < 0, true);
});

test("log ticks are round numbers inside the range, in the unit they are printed in", () => {
  const time = [
    { size: 1, max: 59 },
    { size: 60, max: 59 },
    { size: 3600, max: 900 },
  ];
  const bytes = [2 ** 10, 2 ** 20, 2 ** 30].map((size) => ({ size, max: 900 }));
  assert.deepEqual(logTicks(3600, 36000, time), [3600, 7200, 18000, 36000]);
  assert.deepEqual(logTicks(1.5 * 60, 40 * 60, time), [120, 300, 600, 1200]);
  // Across KiB and MiB each tick is a round number of its own unit.
  assert.deepEqual(
    logTicks(0.4 * 1024, 10 * 2 ** 20, bytes).map((v) => v / 1024),
    [1, 10, 100, 1024, 10240],
  );
  assert.deepEqual(
    logTicks(3.3 * 2 ** 20, 10.3 * 2 ** 20, bytes).map((v) => v / 2 ** 20),
    [4, 5, 6, 8, 10],
  );
  for (const [min, max] of [
    [1, 1000],
    [0.3, 0.9],
    [4e9, 6.5e9],
  ]) {
    const t = logTicks(min, max, [
      { size: 1, max: 900 },
      { size: 1e3, max: 900 },
      { size: 1e6, max: 900 },
      { size: 1e9, max: 900 },
    ]);
    assert.equal(
      t.every((v) => v >= min * (1 - 1e-9) && v <= max * (1 + 1e-9)),
      true,
    );
    assert.deepEqual(
      t,
      [...t].sort((a, b) => a - b),
    );
  }
});

test("log ticks keep their distance on screen and never repeat", () => {
  const bytes = [2 ** 10, 2 ** 20].map((size) => ({ size, max: 900 }));
  const position = (v) => 100 * Math.log(v);
  const crowded = logTicks(700 * 1024, 2 * 2 ** 20, bytes, {
    position,
    gap: 58,
  });
  for (let i = 1; i < crowded.length; i++)
    assert.equal(position(crowded[i]) - position(crowded[i - 1]) >= 58, true);
  // 900 KiB and 1 MiB are 13 px apart here, so only one of them is kept.
  assert.equal(
    crowded.filter((v) => v === 900 * 1024 || v === 2 ** 20).length <= 1,
    true,
  );
  assert.equal(new Set(crowded).size, crowded.length);
  assert.deepEqual(logTicks(10, 20, [{ size: 1, max: 900 }]), [10, 12, 15, 20]);
});

test("linear ticks use the step nearest the target spacing", () => {
  const { ticks, step } = linearTicks(0.87475, 0.8750227);
  assert.equal(step, 0.00005);
  assert.deepEqual(ticks, [0.87475, 0.8748, 0.87485, 0.8749, 0.87495, 0.875]);
  assert.deepEqual(linearTicks(0, 1).ticks, [0, 0.2, 0.4, 0.6, 0.8, 1]);
});
