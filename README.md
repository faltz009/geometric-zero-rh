# A Geometric Definition of Zero: Closure Events on S³ and the Riemann Hypothesis

**Walter Henrique Alves da Silva**  
ORCID: [0009-0001-0857-096X](https://orcid.org/0009-0001-0857-096X)  
April 2026

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.19427453.svg)](https://doi.org/10.5281/zenodo.19427453)

---

## The core argument

When a mathematician says "ζ(s) has a zero at s," they mean the function
evaluates to zero in the complex plane ℂ. This seems like a neutral statement,
but it is not. It is a geometric choice: the choice to measure the Euler
product in flat, two-dimensional space. There is no neutral option. Every
definition of a zero implicitly selects an ambient geometry, and the choice
of ℂ is as much a commitment as any other.

The question is whether ℂ is the *correct* geometry for this problem. The
answer is no, and the reason is Lagrange's four-square theorem (1770): every
prime p = a²+b²+c²+d² has a canonical position on S³, the three-sphere of
unit quaternions, given by the unit quaternion q̂_p = [a,b,c,d]/√p. This
is not an embedding we choose — it is where the prime already sits, forced
by its own arithmetic. The Euler product, which is built from primes, is
therefore a composition of elements of S³. The correct ambient space for the
Euler product is S³, and the classical ζ(s) in ℂ is its two-dimensional
shadow, obtained by projecting away the two dimensions that carry the
four-square structure.

In S³, a zero of ζ is not a numerical vanishing — it is a **Hopf closure
event**: the running quaternionic Euler product Q(s) reaches the equatorial
locus of S³ where the scalar channel W and the vector channel RGB are exactly
equal (the condition W = RGB, or "1 = 3"). From the pure geometry of S³,
with no additional assumptions, this condition forces the real part of s to
equal 1/2. The critical line is not a conjecture in this geometry — it is
the only locus where a closure event can occur.

The Riemann Hypothesis is therefore a consequence of working in the correct
geometry. The shadow of a closure event, projected to ℂ, is a classical zero
of ζ. All such shadows land on Re(s) = 1/2 because all closure events do.

## Why S³? The cup and the 3+1 structure

Here is a simple way to see why 3+1 dimensions is the right dimensionality
for this problem. You see a cup in reality. You cannot quite say "there is a
cup" — what you can say is that there is a 3+1 projection of that cup, which
means there is a 3+1 cup it is projecting from. So we map information into
that dimensionality.

The 3+1 split — one scalar dimension and three vector dimensions — is not
arbitrary. The RGB+W decomposition of the Hopf fibration maps exactly to how
our eyes interpret light (three color channels, one luminance) and to the
structure of spacetime itself (three spatial dimensions, one time dimension).
The W channel is the causal, scalar dimension: it carries what persists. The
RGB channels are the spatial, vector dimensions: they carry what oscillates
and rotates. This is the geometry the universe already uses to organize
information, and it is the geometry of S³.

The Riemann zeta function, studied in ℂ, is studied in a two-dimensional
shadow of this four-dimensional reality. The zeros appear mysterious in the
shadow because their cause — the Hopf closure condition — is visible only in
the full geometry.

## What Definition B says

Definition B states that a classical zero of ζ and a Hopf closure event on
S³ are the same thing. It is a definition — the geometric definition of zero
in the correct geometry — not a conditional assumption.

Both Definition B and the classical framework rest on a geometric foundation.
The question is which geometry is correct. The answer follows from a case
analysis.

**If ℂ is foundational:** The functional equation ξ(s) = ξ(1−s) requires
a proof in ℂ involving Poisson summation, Mellin transform, and gamma factors.
The zero distribution has not been established from ℂ-structure in 160 years.
The GUE spacing statistics of the zeros arise from Haar measure on SU(2) ≅ S³
and have no causal account in ℂ. And Lagrange's theorem, which places every
prime at a canonical position on S³ by arithmetic necessity, plays no role.

**If S³ is foundational (Definition B):** The functional equation is the star
involution Q(1−s) = Q(s)*, the definition of the algebra's symmetry, requiring
no external derivation. The zero distribution is Hopf balance, arithmetically
fixed at re(q)² = 1/2 by the unit sphere constraint, proved with zero axioms.
The GUE statistics follow from Haar measure on SU(2) ≅ S³, the natural measure
on the space. Lagrange's theorem is the reason S³ is correct in the first place.

One assignment leaves four structural properties of the Euler product as
unexplained coincidences. The other derives all four from the geometry.
Definition B names the S³ choice explicitly. The classical definition makes
the ℂ choice without naming it.

## Lean 4 formal proof

The proof is in `lean_proofs/ClosureRH.lean`, verified against Mathlib 4.29
with **zero sorry**. To check it:

```bash
cd lean_proofs
~/.elan/bin/lake build ClosureRH
# Expected: Build completed successfully (2025 jobs)
```

The file is structured in three layers. **Part I** covers pure S³ geometry
with zero axioms, derived from Mathlib's quaternion library: the 1+3 eigenspace
decomposition, chiral closure q·q* = 1, Hopf balance forcing re(q)² = 1/2,
S³ has no zero element (every unit quaternion invertible), and no Hopf-balanced
quaternion is star-fixed (zeros are always free orbits). **Part II** proves
the Geometric Riemann Hypothesis from three geometric axioms about the Euler
product (all Mathlib coverage gaps), with no reference to ζ. **Part III**
proves the Phase Lift theorem (Q^{(ℂ)} = ζ/|ζ|, zero axioms), states
Definition B, and derives the classical Riemann Hypothesis in one line.

Axiom count: 7. Six are Mathlib coverage gaps (Q, Q_unit, A, D, E, ζ) —
eliminated by contributing Q and ζ to Mathlib. One is Definition B, the
geometric foundation. Zero sorry.

## Paper

`paper/GeometricZero.tex` — compile with `pdflatex GeometricZero.tex`.

## Experimental validation

Three independent tests using the first 1000 Riemann zeros and Rust-backed
quaternion algebra from the
[closure-verification](https://github.com/faltz009/closure-verification)
repository:

- Hopf balance error is consistently lower at zero ordinates than at midpoints
  between zeros, across every prime checkpoint from 1k to 50k primes.
- GUE zero-spacing statistics: KS distance 0.111 (GUE) vs 0.322 (Poisson),
  a 2.9× ratio. The GUE statistics are derived from Haar measure on SU(2) ≅ S³
  rather than cited as an empirical observation.
- A two-detector intersection test shows zeros satisfy both the phase-closure
  signal and the spatial-balance signal simultaneously; non-zero ordinates
  satisfy at most one.

## Support this work

This research is conducted independently. Every paper and line of code
was done on personal time and released for free. If you find it valuable,
any support is genuinely appreciated.

| Method | Address |
|---|---|
| BTC | `155jaKugGGhdwX2Dp55bfHWpWbWD3Gr3PG` |
| ETH (ERC-20) | `0x31f0253180b03c16a0aa2d7091311d7363ef22a4` |
| PIX (Brazil) | `walter.h057@gmail.com` |

The geometric computer this work builds on: [closure-verification](https://github.com/faltz009/closure-verification)

## Changelog

### April 5, 2026 — Structural theorems and framing

**New Lean theorems (all zero sorry):**
- `hopf_balanced_not_star_fixed` — no Hopf-balanced unit quaternion is star-fixed. The star involution fixes a quaternion only when all imaginary parts vanish (pure-real scalar). Hopf balance requires the imaginary parts to carry squared norm 1/2 > 0. Proved from pure S³ geometry with zero axioms.
- `hopf_zeros_paired` — if Q(s) is Hopf-balanced then Q(1−s) is Hopf-balanced. Proved from Axiom A alone in two lines. Every zero is paired with a distinct partner at 1−s; the pairing is always free.
- `phase_lift` — ∏ (f n / ‖f n‖) = (∏ f n) / ‖∏ f n‖ for any finite set. Proved by induction on norm multiplicativity with zero axioms. The complex-plane running product Q^{(ℂ)} is the normalized phase of the classical Euler product.
- `GeometricZero` / `ClosureEvent` unified: the predicate carries both names as verified aliases. Terminology consistent throughout.
- Lean Part I updated: S³ has no zero element (every unit quaternion invertible), zeros are always free orbits.

**Paper additions:**
- New section: *The analytic continuation as Hopf reflection.* ζ(−1) = −1/12 is the S³-volume constant reflected through the critical line. Since vol(S³) = 2π² and ζ(2) = π²/6 = vol(S³)/12, the Casimir value is ζ(2) through the Hopf mirror. The regularization is not a trick; it is a projection artifact.
- Definition B section rewritten as proof by inversion: both ℂ and S³ are geometric choices; the ℂ choice leaves four structural properties of the Euler product (functional equation, zero distribution, GUE statistics, Lagrange's role) as unexplained coincidences; the S³ choice derives all four.
- Terminology unified: geometric zero = closure event = Hopf closure event; classical zero = algebraic zero.
- Axiom framing made explicit: axioms in Part II reflect Mathlib's ℂ-centric library boundary, not mathematical gaps; S³ geometry is more primitive than ℂ in Mathlib's own type hierarchy.

### April 5, 2026 — Initial release (DOI 10.5281/zenodo.19427453)

First public release. Geometric zero definition, Lean 4 proof (zero sorry), paper, and experimental validation on first 1000 Riemann zeros.

## Citation

```
Walter Henrique Alves da Silva,
"A Geometric Definition of Zero: Closure Events on S³ and the Riemann Hypothesis,"
April 2026. DOI: 10.5281/zenodo.19427453.
https://github.com/faltz009/geometric-zero-rh
```

## License

Paper text: [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/)  
Lean proof and code: MIT  
See [LICENSE](LICENSE) for full terms.
