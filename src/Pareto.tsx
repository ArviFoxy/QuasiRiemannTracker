import { useEffect, useMemo, useRef, useState } from "react";
import { Maximize2, Search } from "lucide-react";
import { decimal, relativePosition } from "../core/rational.mjs";
import {
  inScale,
  linearTicks,
  logTicks,
  paretoFront,
  thetaDomain,
} from "../core/pareto.mjs";
import { measureById, measures } from "../core/proof-size.mjs";
import { boundLabel } from "../core/catalogue.mjs";
import { proofRevision } from "../core/catalogue-revisions.mjs";
import type { Contribution, SizeData } from "./types";

type Point = {
  id: string;
  theta: Contribution["theta"];
  size: number;
  record: Contribution;
};
const H = 400,
  L = 84,
  R = 24,
  T = 44,
  B = 62;
const teal = "#1d5d74",
  gray = "#82959e",
  surface = "#fbfcfc";

export default function Pareto({
  records,
  sizes,
  loading,
  measure: requested,
  onMeasure,
  selected,
  onSelect,
}: {
  records: Contribution[];
  sizes: SizeData | null;
  loading: boolean;
  measure: string | null;
  onMeasure: (id: string) => void;
  selected: string | null;
  onSelect: (id: string) => void;
}) {
  const entries = sizes?.entries ?? {};
  const available = (m: (typeof measures)[number]) =>
    records.filter((r) => m.value(entries[proofRevision(r)] ?? {}) > 0).length;
  // Measured costs are the point of this view; fall back to what can be counted.
  const fallback =
    measures.find((m) => available(m) > 0 && available(m) >= records.length / 2) ??
    measures[3];
  const measure =
    (requested && measureById(requested)) || fallback;
  const points: Point[] = useMemo(
    () =>
      records.flatMap((record) => {
        const size = measure.value(entries[proofRevision(record)] ?? {});
        return size > 0
          ? [{ id: record.id, theta: record.theta, size, record }]
          : [];
      }),
    [records, entries, measure],
  );
  const missing = records.length - points.length;
  const { front, onFront, dominators } = useMemo(
    () => paretoFront(points),
    [points],
  );
  const [fitAll, setFitAll] = useState(false);
  const [hover, setHover] = useState<Point | null>(null);
  const svg = useRef<SVGSVGElement>(null);
  const [W, setWidth] = useState(800);
  useEffect(() => {
    const el = svg.current?.parentElement;
    if (!el) return;
    const observer = new ResizeObserver(([entry]) =>
      setWidth(Math.max(280, entry.contentRect.width)),
    );
    observer.observe(el);
    return () => observer.disconnect();
  }, []);
  const width = W - L - R,
    height = H - T - B;
  const near = points.filter(inScale);
  // Weaker than the OpenAI baseline would flatten the rest, so they sit on the
  // top edge unless the reader asks to see everything.
  const shown = fitAll || !near.length ? points : near;
  const { low, high } = useMemo(
    () =>
      shown.length
        ? thetaDomain(shown.map((p) => p.theta))
        : {
            low: { numerator: "87", denominator: "100" },
            high: { numerator: "22", denominator: "25" },
          },
    [shown],
  );
  const xs = shown.map((p) => p.size),
    xMin = xs.length ? Math.min(...xs) * 0.85 : 1,
    xMax = xs.length ? Math.max(...xs) * 1.18 : 10;
  const logSpan = Math.log(xMax) - Math.log(xMin) || 1;
  const x = (size: number) =>
    L + Math.max(0, Math.min(1, (Math.log(size) - Math.log(xMin)) / logSpan)) * width;
  const y = (theta: Point["theta"]) =>
    T + height * (1 - Math.max(-0.15, Math.min(1.15, relativePosition(theta, low, high))));
  const lowN = Number(decimal(low, 15).replace("…", "")),
    highN = Number(decimal(high, 15).replace("…", ""));
  const yTicks = useMemo(() => linearTicks(lowN, highN, 5), [lowN, highN]);
  const decimals = Math.max(0, Math.ceil(-Math.log10(yTicks.step) - 1e-9));
  const yAt = (value: number) => T + height * (1 - (value - lowN) / (highN - lowN));
  const xTicks = useMemo(
    () => (xs.length ? logTicks(xMin, xMax, measure.tickScale(xMax)) : []),
    [xs.length, xMin, xMax, measure],
  );
  const offScale = (p: Point) => !fitAll && near.length > 0 && !inScale(p);
  const steps = front.filter((p) => !offScale(p));
  let path = "";
  steps.forEach((p, i) => {
    path += i ? ` H ${x(p.size)} V ${y(p.theta)}` : `M ${x(p.size)} ${y(p.theta)}`;
  });
  if (steps.length) path += ` H ${W - R}`;
  const label = (p: Point) => {
    const [first, ...others] = p.record.authors.map((a) => a.name);
    return others.length ? `${first} et al.` : first;
  };
  // Estimated, not measured: enough to keep a label inside the plot.
  const textWidth = (text: string) => text.length * 6.6;
  const flip = (p: Point) => x(p.size) + 10 + textWidth(label(p)) > W - R;
  const offLabel = (p: Point) =>
    `θ = ${+Number(decimal(p.theta, 12).replace("…", "")).toPrecision(4)}`;
  const best = steps[steps.length - 1];
  const labelled = new Set(
    [steps[0], best, points.find((p) => p.id === selected)]
      .filter(Boolean)
      .map((p) => p!.id),
  );
  const ordered = [...points].sort((a, b) => a.size - b.size);
  const focusNeighbour = (id: string, step: number) => {
    const next = ordered[ordered.findIndex((p) => p.id === id) + step];
    if (next)
      svg.current
        ?.querySelector<SVGGElement>(`[data-pareto-id="${CSS.escape(next.id)}"]`)
        ?.focus();
  };
  const dominatedBy = (p: Point) => dominators.get(p.id)?.[0]?.record.title;
  // Beside the point it describes, on whichever side has room.
  const tooltipStyle = (p: Point): React.CSSProperties => {
    const px = x(p.size),
      py = offScale(p) ? T - 16 : y(p.theta),
      right = px > W * 0.55;
    return {
      ...(right ? { right: W - px + 14 } : { left: px + 14 }),
      ...(py < 150 ? { top: py + 14 } : { bottom: H - py + 14 }),
      maxWidth: Math.max(160, (right ? px : W - px) - 22),
    };
  };
  return (
    <section className="panel chart-panel pareto-panel" aria-label="Bound against proof size">
      <div className="pareto-controls">
        <label className="pareto-measure">
          <span>Proof size</span>
          <select
            value={measure.id}
            onChange={(event) => onMeasure(event.target.value)}
          >
            {measures.map((m) => (
              <option key={m.id} value={m.id} disabled={!available(m)}>
                {m.label}
                {available(m) ? "" : " (not measured yet)"}
              </option>
            ))}
          </select>
        </label>
        <div className="chart-tools">
          <button
            className="icon"
            aria-label="Zoom to the baseline range"
            aria-pressed={!fitAll}
            title="Zoom to bounds at or below the OpenAI baseline, 7/8"
            onClick={() => setFitAll(false)}
          >
            <Search size={16} />
          </button>
          <button
            className="icon"
            aria-label="Show every bound"
            aria-pressed={fitAll}
            title="Show every bound, including those weaker than 7/8"
            onClick={() => setFitAll(true)}
          >
            <Maximize2 size={16} />
          </button>
        </div>
      </div>
      <p className="pareto-note">
        {measure.note} A result is on the Pareto front when no other result has
        both a stronger bound and a smaller proof.
      </p>
      <div className="chart-wrap">
        <svg
          ref={svg}
          viewBox={`0 0 ${W} ${H}`}
          className="chart pareto-chart"
          role="group"
          aria-label={`Bound θ against ${measure.label.toLowerCase()}, both smaller is better. Tab to move between results; left and right arrows jump to the next smaller or larger proof.`}
        >
          {yTicks.ticks.map((t) => (
            <g key={t}>
              <line x1={L} x2={W - R} y1={yAt(t)} y2={yAt(t)} stroke="#e1e7ea" />
              <text x={L - 12} y={yAt(t) + 4} textAnchor="end" className="axis" data-axis="bound">
                {t.toFixed(decimals)}
              </text>
            </g>
          ))}
          {xTicks.map((t) => (
            <g key={t}>
              <line x1={x(t)} x2={x(t)} y1={T} y2={H - B} stroke="#e1e7ea" />
              <text x={x(t)} y={H - B + 20} textAnchor="middle" className="axis" data-axis="size">
                {measure.format(t)}
              </text>
            </g>
          ))}
          <text x={L - 12} y={T - 14} textAnchor="end" className="axis-label">
            θ
          </text>
          <text x={L + width / 2} y={H - 10} textAnchor="middle" className="axis-label">
            {measure.label} · log scale
          </text>
          {!points.length && !loading && (
            <text x={L + width / 2} y={T + height / 2} textAnchor="middle" className="axis-label">
              No results have this measurement yet.
            </text>
          )}
          {path && (
            <path
              className="pareto-front"
              d={path}
              fill="none"
              stroke={teal}
              strokeWidth="2"
              strokeLinejoin="round"
            />
          )}
          {[...points]
            .sort((a, b) => Number(onFront.has(a.id)) - Number(onFront.has(b.id)))
            .map((p) => {
              const front = onFront.has(p.id);
              const off = offScale(p);
              const px = x(p.size),
                py = off ? T - 16 : y(p.theta);
              const isSelected = selected === p.id;
              const color = front ? teal : gray;
              return (
                <g
                  key={p.id}
                  data-pareto-id={p.id}
                  data-front={front}
                  className="dot pareto-point"
                  role="button"
                  tabIndex={0}
                  aria-label={`${p.record.title}, theta ${boundLabel(p.record)}, ${measure.short.toLowerCase()} ${measure.format(p.size)}`}
                  aria-description={
                    front
                      ? "On the Pareto front"
                      : `Dominated by ${dominatedBy(p) ?? "another result"}`
                  }
                  aria-pressed={isSelected}
                  onClick={() => onSelect(p.id)}
                  onKeyDown={(e) => {
                    if (e.key === "Enter" || e.key === " ") {
                      e.preventDefault();
                      onSelect(p.id);
                    } else if (e.key === "ArrowRight" || e.key === "ArrowLeft") {
                      e.preventDefault();
                      focusNeighbour(p.id, e.key === "ArrowRight" ? 1 : -1);
                    }
                  }}
                  onFocus={() => setHover(p)}
                  onBlur={() => setHover(null)}
                  onMouseEnter={() => setHover(p)}
                  onMouseLeave={() => setHover(null)}
                >
                  <circle cx={px} cy={py} r={16} fill="transparent" />
                  {isSelected && <circle cx={px} cy={py} r={13} fill={`${teal}22`} />}
                  <circle cx={px} cy={py} r={7} fill={surface} />
                  {off ? (
                    <path
                      d={`M ${px} ${py - 5} L ${px + 5.5} ${py + 4} L ${px - 5.5} ${py + 4} Z`}
                      fill={front ? teal : gray}
                      strokeLinejoin="round"
                    />
                  ) : (
                    <circle cx={px} cy={py} r={5} fill={color} />
                  )}
                </g>
              );
            })}
          {W > 600 && (
            <g aria-hidden="true" pointerEvents="none">
              {points.map((p) => {
                const off = offScale(p);
                if (!off && !labelled.has(p.id)) return null;
                const px = x(p.size);
                return off ? (
                  <text key={p.id} x={px + 10} y={T - 12} className="point-label">
                    {offLabel(p)}
                  </text>
                ) : (
                  <text
                    key={p.id}
                    x={flip(p) ? px - 10 : px + 10}
                    y={y(p.theta) - 10}
                    textAnchor={flip(p) ? "end" : "start"}
                    className="point-label"
                  >
                    {label(p)}
                  </text>
                );
              })}
            </g>
          )}
        </svg>
        {hover && (
          <div className="chart-tooltip" role="status" style={tooltipStyle(hover)}>
            <strong>{hover.record.title}</strong>
            <span>
              θ = {boundLabel(hover.record)} · {measure.short.toLowerCase()}{" "}
              {measure.format(hover.size)}
            </span>
            <small>
              {onFront.has(hover.id)
                ? "On the Pareto front"
                : `Dominated by ${dominatedBy(hover) ?? "another result"}`}
              {offScale(hover) ? " · weaker than the OpenAI baseline" : ""}
            </small>
          </div>
        )}
      </div>
      <div className="chart-bottom">
        <span>
          <i className="legend-dot front" />
          On the Pareto front
        </span>
        <span>
          <i className="legend-dot" />
          Dominated by another result
        </span>
        {!fitAll && near.length < points.length && (
          <span>
            <i className="legend-triangle" />
            Weaker than the OpenAI baseline, drawn at the top
          </span>
        )}
      </div>
      {missing > 0 && (
        <p className="chart-note">
          {missing} verified {missing === 1 ? "result has" : "results have"} no{" "}
          {measure.short.toLowerCase()} measurement yet and{" "}
          {missing === 1 ? "is" : "are"} not plotted.
        </p>
      )}
      {sizes?.profile && measure.id !== "modules" && measure.id !== "lines" && (
        <p className="chart-note">
          Measured with Lean {sizes.profile.lean_version} on {sizes.profile.machine.cpu},{" "}
          {sizes.profile.machine.cores} cores.
        </p>
      )}
      <details className="pareto-table">
        <summary>Table view</summary>
        <table>
          <thead>
            <tr>
              <th scope="col">Result</th>
              <th scope="col">Exact bound θ</th>
              <th scope="col">{measure.short}</th>
              <th scope="col">Pareto front</th>
            </tr>
          </thead>
          <tbody>
            {ordered.map((p) => (
              <tr key={p.id} className={selected === p.id ? "selected" : undefined}>
                <th scope="row">
                  <button onClick={() => onSelect(p.id)}>{p.record.title}</button>
                </th>
                <td>{boundLabel(p.record)}</td>
                <td>{measure.format(p.size)}</td>
                <td>
                  {onFront.has(p.id)
                    ? "Yes"
                    : `No, dominated by ${dominatedBy(p) ?? "another result"}`}
                </td>
              </tr>
            ))}
          </tbody>
        </table>
      </details>
    </section>
  );
}
