import type { Rational } from "./types";

export const milestones: {
  id: string;
  label: string;
  decimal: string;
  theta: Rational;
  dashed: boolean;
  title: string;
  description: string;
  technical: string;
  source: { label: string; url: string };
}[] = [
  {
    id: "one",
    label: "1",
    decimal: "1.0",
    theta: { numerator: "1", denominator: "1" },
    dashed: false,
    title: "Classical result",
    description:
      "The classical result puts all nontrivial zeros in the strip between real parts 0 and 1.",
    technical: String.raw`Absolute convergence of the Euler product gives \(L(s,\chi)\ne0\) for \(\operatorname{Re}s>1\). A uniform bound \(\theta<1\), independent of conductor and height, establishes the Dirichlet quasi-Riemann hypothesis. The functional equation then confines nontrivial zeros to \(1-\theta\le\operatorname{Re}s\le\theta\).`,
    source: {
      label: "OpenAI, introduction and continuation principle",
      url: "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L45",
    },
  },
  {
    id: "thirteen-fifteenths",
    label: "13/15",
    decimal: "0.8666…",
    theta: { numerator: "13", denominator: "15" },
    dashed: true,
    title: "Limit of OpenAI’s method",
    description:
      "OpenAI’s approach combines several refined estimates. Its bound can be improved by tuning parameters and improving the functions used to count zeros. An analysis of the current approach places its limit at 13/15 = 0.8666…: these improvements can bring the bound toward this value, but reaching or crossing it requires a new ingredient in the argument.",
    technical: String.raw`In the analyzed cubic-theta exponent model, the normalization \(M+\ell=1\) and the near-critical-line row count \(R(0)=1\) force \(\theta>13/15\), even with density-hypothesis-strength counts. The obstruction concerns this model of the method; the analysis optimistically extends some exponent formulas beyond their proved ranges.`,
    source: {
      label: "tomoto0, barrier analysis §2",
      url: "https://github.com/tomoto0/quasi-riemann-hypothesis-7-8-verification/blob/b83a73c6cb626a391e551baafdb7d0cceafaa55a/reports/barrier_analysis.md",
    },
  },
  {
    id: "three-quarters",
    label: "3/4",
    decimal: "0.75",
    theta: { numerator: "3", denominator: "4" },
    dashed: true,
    title: "Halfway to the critical line",
    description:
      "At ¾, the region where zeros can occur is half as wide as in the classical result. Its two edges have moved halfway toward the central line. Beating ¾ would squeeze the zeros into an even narrower region around that line.",
    technical: String.raw`A uniform zero-free half-plane \(\operatorname{Re}s>3/4\), together with the functional equation, confines all nontrivial Dirichlet zeros to \(1/4\le\operatorname{Re}s\le3/4\). The admissible strip has width \(2\theta-1=1/2\). This threshold is a geometric milestone; a method-specific obstruction at \(\theta=3/4\) would require a separate proof.`,
    source: {
      label: "OpenAI, functional-equation consequence",
      url: "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L310",
    },
  },
  {
    id: "half",
    label: "1/2",
    decimal: "0.5",
    theta: { numerator: "1", denominator: "2" },
    dashed: false,
    title: "Generalized Riemann Hypothesis",
    description:
      "At ½, the allowed strip closes to a single line. Every nontrivial zero must lie exactly on it. Reaching this goal would prove the Riemann hypothesis and its extension to all Dirichlet L-functions, giving much sharper control over the distribution of primes.",
    technical: String.raw`If \(L(s,\chi)\ne0\) for every Dirichlet character \(\chi\) and every \(\operatorname{Re}s>1/2\), with the principal pole excluded, functional-equation symmetry forces \(\operatorname{Re}\rho=1/2\) for every nontrivial zero \(\rho\). This is GRH for Dirichlet L-functions; the modulus-one case is RH for \(\zeta(s)\).`,
    source: {
      label: "OpenAI, introduction and functional-equation consequence",
      url: "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L98",
    },
  },
];
