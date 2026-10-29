const M = require('./math.js');
const { E, primaryPrimes, gauss, mod } = M;
const P = primaryPrimes(120);
console.log('primes:', P.map(f => `${f.pi[0]}+${f.pi[1]}ω (N=${f.p})`).join(', '));
const abs = ([a, b]) => Math.hypot(a, b);
let worst = 0, cnt = 0;
// 1. flat spectrum |g(π,h)| = √p off πO, 0 on πO; and g(π,h) = conj χ(h)·g(π,1)
for (const f of P.slice(0, 8)) {
  const g1 = gauss([f], [1, 0]);
  for (let a = -6; a <= 6; a++) for (let b = -6; b <= 6; b++) {
    const h = [a, b]; const g = gauss([f], h); const k = f.chiK(h);
    if (k < 0) { worst = Math.max(worst, abs(g)); cnt++; continue; }
    worst = Math.max(worst, Math.abs(abs(g) - Math.sqrt(f.p)));
    const ph = -2 * Math.PI * k / 6;                       // conj χ(h)
    const pred = [g1[0] * Math.cos(ph) - g1[1] * Math.sin(ph), g1[0] * Math.sin(ph) + g1[1] * Math.cos(ph)];
    worst = Math.max(worst, abs([g[0] - pred[0], g[1] - pred[1]]));
    cnt++;
  }
}
console.log('flat spectrum + dilation: cases', cnt, 'max error', worst.toExponential(2));

// 2. transfer identity g(Dn,h) = ε g(D,h) g(n,D⁴h), ε = χ_D(n)/χ_n(D) = ±1 for primary D,n
worst = 0; cnt = 0; const eps = {};
for (let i = 0; i < 6; i++) for (let j = 0; j < 6; j++) {
  const D = P[i], n = P[j]; if (D.p === n.p) continue;
  const kDn = D.chiK(n.pi), knD = n.chiK(D.pi);
  const ke = mod(kDn - knD, 6); eps[ke] = (eps[ke] || 0) + 1;
  const e = [Math.cos(2 * Math.PI * ke / 6), Math.sin(2 * Math.PI * ke / 6)];
  for (const h of [[1, 0], [2, 1], [-3, 2], [5, -4], [4, 4], [D.pi[0], D.pi[1]]]) {
    const lhs = gauss([D, n], h);
    const gD = gauss([D], h), gn = gauss([n], E.mul(E.pow(D.pi, 4), h));
    const pr = [gD[0] * gn[0] - gD[1] * gn[1], gD[0] * gn[1] + gD[1] * gn[0]];
    const rhs = [e[0] * pr[0] - e[1] * pr[1], e[0] * pr[1] + e[1] * pr[0]];
    worst = Math.max(worst, abs([lhs[0] - rhs[0], lhs[1] - rhs[1]]) / Math.max(1, abs(lhs)));
    cnt++;
  }
}
console.log('transfer identity: cases', cnt, 'max rel error', worst.toExponential(2), 'eps exponents', eps);

// 3. comb: g(D²,h) nonzero iff v_D(h) = 1, then |g| = p^{3/2}
worst = 0; cnt = 0; let support = 0;
const D = P[0];
for (let a = -9; a <= 9; a++) for (let b = -9; b <= 9; b++) {
  const h = [a, b]; const g = gauss([D, D], h);
  // valuation of h at D
  let v = 0, hh = h;
  const divides = (x) => D.chiK(x) < 0;
  if (a === 0 && b === 0) continue;
  // compute v_D(h) by dividing: x divisible by D iff red(x)=0; divide via conj trick
  while (divides(hh) && v < 5) { // hh = hh / D = hh * conj(D) / p
    const t = E.mul(hh, E.conj(D.pi)); hh = [t[0] / D.p, t[1] / D.p]; v++;
  }
  const expect = v === 1 ? Math.pow(D.p, 1.5) : 0;
  worst = Math.max(worst, Math.abs(abs(g) - expect)); cnt++; if (v === 1) support++;
}
console.log('comb D²: cases', cnt, 'support', support, 'max error', worst.toExponential(2));
