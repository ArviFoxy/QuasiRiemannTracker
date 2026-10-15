import { milestones } from "./milestones";
import { MathJax } from "better-react-mathjax";

export default function Milestones() {
  return (
    <section className="milestones" aria-labelledby="milestones-heading">
      <h2 id="milestones-heading">From one to the critical line</h2>
      <p className="milestones-intro">
        The Riemann Hypothesis predicts that every nontrivial zero of the Riemann
        zeta function has real part ½. The Generalized Riemann Hypothesis makes
        the same prediction for Dirichlet L-functions. The quasi-Riemann
        hypothesis allows their nontrivial zeros to lie anywhere in a strip
        between 1 − θ and θ, for some fixed θ &lt; 1. Lowering θ toward ½ narrows
        this strip until it becomes the line predicted by GRH. Getting there
        means overcoming several barriers in the proof methods.
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
