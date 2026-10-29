// Eisenstein integers x = a + b·ω, ω = e^{2πi/3}, stored as [a, b].
const SQ3 = Math.sqrt(3);
const E = {
  mul: ([a, b], [c, d]) => [a * c - b * d, a * d + b * c - b * d],
  add: ([a, b], [c, d]) => [a + c, b + d],
  norm: ([a, b]) => a * a - a * b + b * b,
  conj: ([a, b]) => [a - b, -b],
  cx: ([a, b]) => [a - b / 2, (b * SQ3) / 2],
  pow(x, k) { let r = [1, 0]; for (let i = 0; i < k; i++) r = E.mul(r, x); return r; },
};
// sixth roots of unity as units: exponent k ↦ e^{2πik/6}
const UNIT = [[1, 0], [1, 1], [0, 1], [-1, 0], [-1, -1], [0, -1]];

function modpow(b, e, m) {
  let r = 1; b %= m; if (b < 0) b += m;
  while (e > 0) { if (e & 1) r = (r * b) % m; b = (b * b) % m; e >>= 1; }
  return r;
}
function modinv(a, m) { return modpow(((a % m) + m) % m, m - 2, m); }
const mod = (a, m) => ((a % m) + m) % m;

function isPrime(n) { if (n < 2) return false; for (let d = 2; d * d <= n; d++) if (n % d === 0) return false; return true; }

// A prime π of ℤ[ω] with N(π) = p ≡ 1 (mod 3), normalised primary (π ≡ 2 mod 3).
function makePrime(pi) {
  const p = E.norm(pi);
  const [a, b] = pi;
  const r = mod(-a * modinv(b, p), p);         // ω ↦ r in O/(π) ≅ F_p
  if (mod(r * r + r + 1, p) !== 0) throw new Error('bad r');
  const img = UNIT.map(([u, v]) => mod(u + v * r, p));
  const red = ([c, d]) => mod(c + d * r, p);
  const e6 = (p - 1) / 6;
  // sextic residue symbol exponent: (x/π)_6 = e^{2πik/6}, or -1 for x ≡ 0
  const chiK = (x) => { const z = red(x); if (z === 0) return -1; const t = modpow(z, e6, p); return img.indexOf(t); };
  return { pi, p, r, red, chiK };
}

function primaryPrimes(maxNorm) {
  const out = [];
  for (let p = 7; p <= maxNorm; p++) {
    if (!isPrime(p) || p % 3 !== 1) continue;
    const found = [];
    for (let a = -20; a <= 20; a++) for (let b = -20; b <= 20; b++) {
      if (E.norm([a, b]) !== p) continue;
      if (mod(a, 3) !== 2 || mod(b, 3) !== 0) continue;   // primary
      if (!found.some(q => q[0] === a && q[1] === b)) found.push([a, b]);
    }
    // two non-associate primaries per split p (π and its conjugate)
    for (const f of found) out.push(makePrime(f));
  }
  return out;
}

// additive character phase: Tr(h·x / (s·√−3)) ∈ ℚ, character = e^{2πi·tr}
function trPhase(h, x, s) {
  const [hr, hi] = E.cx(h), [xr, xi] = E.cx(x), [sr, si] = E.cx(s);
  const nr = hr * xr - hi * xi, ni = hr * xi + hi * xr;   // h·x
  const dr = -SQ3 * si, di = SQ3 * sr;                     // s·i√3
  const dd = dr * dr + di * di;
  const zr = (nr * dr + ni * di) / dd;                     // Re(num/den)
  return 2 * zr;
}
const cis = (t) => [Math.cos(2 * Math.PI * t), Math.sin(2 * Math.PI * t)];

// Gauss sum g(s,h) = Σ_{x mod s} χ_s(x) ψ_s(hx) for a modulus given as a list of prime factors
// (distinct primes, or one prime squared). Representatives: rational integers 0..N(s)-1.
function gauss(factors, h) {
  let s = [1, 0], N = 1;
  for (const f of factors) { s = E.mul(s, f.pi); N *= f.p; }
  let re = 0, im = 0;
  for (let x = 0; x < N; x++) {
    let k = 0, zero = false;
    for (const f of factors) { const kk = f.chiK([x, 0]); if (kk < 0) { zero = true; break; } k += kk; }
    if (zero) continue;
    const t = trPhase(h, [x, 0], s) + k / 6;
    re += Math.cos(2 * Math.PI * t); im += Math.sin(2 * Math.PI * t);
  }
  return [re, im];
}

module.exports = { E, UNIT, modpow, mod, makePrime, primaryPrimes, trPhase, gauss, cis };
