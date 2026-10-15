import type { Rational } from "./types";

export const milestones: {
  id: string;
  label: string;
  decimal: string;
  theta: Rational;
  dashed: boolean;
  title: string;
  kind: string;
  description: string;
  significance: string;
  source: { label: string; url: string };
}[] = [
  {
    id: "one",
    label: "1",
    decimal: "1.0",
    theta: { numerator: "1", denominator: "1" },
    dashed: false,
    title: "A fixed gap below one",
    kind: "Classical boundary",
    description:
      "The Euler product gives nonvanishing for Re(s) > 1. A fixed θ < 1 excludes zeros from a strip of positive width, uniformly over all heights and Dirichlet characters.",
    significance:
      "Crossing this boundary establishes the uniform Dirichlet quasi-Riemann hypothesis, already achieved by the tracker's verified results.",
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
    title: "The row-counting obstruction",
    kind: "Barrier in the analyzed method",
    description:
      "An independent analysis of the cubic-theta method finds θ > 13/15 under its fixed normalization and exponent model. Auxiliary rows with zeros near the critical line exhaust the counting saving, even with density-hypothesis-strength counts.",
    significance:
      "Reaching or crossing 13/15 would require overcoming an assumption or estimate in that model. The threshold describes the analyzed proof strategy; its derivation extrapolates some estimates beyond their proved ranges.",
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
    title: "Halving the possible zero strip",
    kind: "Intermediate milestone",
    description:
      "At θ = 3/4, the functional equation confines nontrivial Dirichlet zeros to 1/4 ≤ Re(s) ≤ 3/4, halving the classical strip's width. Crossing 3/4 narrows it further.",
    significance:
      "This marks progress toward the critical line. A method-specific obstruction at θ = 3/4 needs a separate argument: the paper's internal parameter κ = 3/4 corresponds to θ = 7/8.",
    source: {
      label: "OpenAI, functional equation and fourth-moment parameter range",
      url: "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L12532",
    },
  },
  {
    id: "half",
    label: "1/2",
    decimal: "0.5",
    theta: { numerator: "1", denominator: "2" },
    dashed: false,
    title: "The critical line",
    kind: "Goal · Dirichlet GRH",
    description:
      "At θ = 1/2, nonvanishing to the right and functional-equation symmetry place every nontrivial Dirichlet zero on the critical line Re(s) = 1/2.",
    significance:
      "Reaching this goal proves the generalized Riemann hypothesis for Dirichlet L-functions, including the Riemann hypothesis for ζ(s).",
    source: {
      label: "OpenAI, introduction and functional-equation consequence",
      url: "https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex#L98",
    },
  },
];
