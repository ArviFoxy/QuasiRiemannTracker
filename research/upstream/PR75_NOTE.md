# Upstream PR 75 (Runbo Li, "acyclic natural-tail feedback", 0.87469284): note (2026-10-25)

- **What it does.** It uses Sil's PR 74 theorem (β ≤ 0.8746935) as an established prior. That
  lowers the natural moment cost to `K = 6(2β − 1) ≈ 4.4963`, strengthens the tail, and leads to a
  regenerated return: 108 rectangles, 21 windows, 423 Bernstein certificates.
- **Gain.** 6.6e-7 over PR 74. It is behind our PR 76 (0.8746075) by 8.5e-5.
- **Credits.** It credits ArviFoxy for the return algebra and the certificate tooling.
- **For us.** This is the natural-cost bootstrap we priced at about 2e-7 for our chain
  (`dθ*/dK ≈ 6e-5`). Sil's native κ stays at 3/4, because the OpenAI certificate requires
  `κ ≥ 3/4`. With κ = 2θ − 1 from our own bound, Sil's slope floor would move only from 26/7 to
  3.7133, worth about 1e-6.
- **The bar.** Our PR 76 (0.8746075) is now the best upstream entry. The next target is
  ≤ 0.8745975.
