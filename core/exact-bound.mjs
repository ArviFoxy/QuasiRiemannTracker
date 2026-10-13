import { rational } from "./rational.mjs";

// Canonical algebraic expressions are fixed verifier profiles. Submitted text
// is matched exactly; it is never interpolated into Lean code.
const liu = {
  label: "(1507 − 2√921) / 1653",
  lean: "(1507 - 2 * Real.sqrt 921) / 1653",
  interval: {
    lower: {
      numerator: "437478534899584370009170003479",
      denominator: "500000000000000000000000000000",
    },
    upper: {
      numerator: "874957069799168740018340006959",
      denominator: "1000000000000000000000000000000",
    },
  },
};
export function exactBound(label) {
  const fraction = /^(\d+)\/(\d+)$/.exec(label ?? "");
  if (fraction) {
    const theta = rational(fraction[1], fraction[2]);
    if (BigInt(theta.numerator) <= 0n) throw Error("Bound must be positive");
    return { theta, lean: `${theta.numerator} / ${theta.denominator}` };
  }
  if (label === liu.label) {
    // Certify the decimal enclosure by integer inequalities for sqrt(921).
    // For r = n/d, x > r iff (1507d - 1653n)^2 > 4*921*d^2,
    // with 1507d - 1653n positive. The reverse inequality certifies x < r.
    for (const [side, r] of Object.entries(liu.interval)) {
      const n = BigInt(r.numerator),
        d = BigInt(r.denominator);
      const a = 1507n * d - 1653n * n;
      const delta = a * a - 4n * 921n * d * d;
      if (a <= 0n || (side === "lower" ? delta <= 0n : delta >= 0n))
        throw Error("Invalid algebraic profile enclosure");
    }
    return {
      theta: structuredClone(liu.interval.upper),
      exact_bound: liu.label,
      bound_interval: structuredClone(liu.interval),
      lean: liu.lean,
    };
  }
  throw Error("This exact expression requires an algebraic checking profile");
}
