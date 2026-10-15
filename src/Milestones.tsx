import { milestones } from "./milestones";

export default function Milestones() {
  return (
    <section className="milestones" aria-labelledby="milestones-heading">
      <h2 id="milestones-heading">From one to the critical line</h2>
      <p className="milestones-intro">
        A bound θ excludes zeros with Re(s) &gt; θ for every Dirichlet
        L-function. Smaller values give a larger zero-free region.
      </p>
      <ol className="milestone-list">
        {milestones.map((m) => (
          <li key={m.id}>
            <div className="milestone-value">
              <span
                className={`milestone-swatch${m.dashed ? " dashed" : ""}`}
                aria-hidden="true"
              />
              <strong>{m.label}</strong>
              <small>{m.decimal}</small>
            </div>
            <article>
              <span className="eyebrow">{m.kind}</span>
              <h3>{m.title}</h3>
              <p>{m.description}</p>
              <p>{m.significance}</p>
              <a
                className="milestone-source"
                href={m.source.url}
                target="_blank"
                rel="noreferrer"
              >
                {m.source.label}
              </a>
            </article>
          </li>
        ))}
      </ol>
    </section>
  );
}
