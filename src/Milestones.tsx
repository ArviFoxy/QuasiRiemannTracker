import { milestones } from "./milestones";
import { MathJax } from "better-react-mathjax";

export default function Milestones() {
  return (
    <section className="milestones" aria-labelledby="milestones-heading">
      <h2 id="milestones-heading">From one to the critical line</h2>
      <p className="milestones-intro">
        These functions encode patterns in prime numbers. The bound tells us how
        far to the right their zeros can lie. Lowering it brings us closer to
        proving that every nontrivial zero lies on one central line.
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
              <h3>{m.title}</h3>
              <p>{m.description}</p>
              <MathJax dynamic>
                <p>{m.technical}</p>
              </MathJax>
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
