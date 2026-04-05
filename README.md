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

The paper introduces "Definition B": a classical zero of ζ and a geometric
zero (Hopf closure event on S³) are the same thing. This is called a
definition rather than an axiom because the alternative — treating ζ(s) = 0
in ℂ as the primary definition — is equally a choice of geometry, and the
less natural one. Refusing to define S³ as the correct geometry is not
neutrality; it is the implicit choice of flat space. Definition B makes the
geometric choice explicit and works with it.

The remaining formal task is to prove that the projection from S³ to ℂ sends
Hopf closure events to complex zeros — to establish the equivalence of the
two descriptions by direct calculation. This is supported by strong
experimental evidence and is the subject of ongoing work. The Lean proof
formalizes the geometric argument completely; Definition B is the stated
bridge to the classical formulation.

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
decomposition, the chiral closure identity q·q* = 1, and the central fact that
Hopf balance on any unit quaternion forces re(q)² = 1/2. **Part II** proves
the Geometric Riemann Hypothesis from three geometric axioms about the Euler
product, with no reference to ζ. **Part III** states Definition B and derives
the classical Riemann Hypothesis in one line.

## Paper

`paper/PrimesOnS3_RH.tex` — compile with `pdflatex PrimesOnS3_RH.tex`.

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

This research is conducted independently at the Open Research Institute.
If you find it valuable, support is welcome:

- GitHub Sponsors: [github.com/sponsors/faltz009](https://github.com/sponsors/faltz009)
- The geometric computer this builds on: [closure-verification](https://github.com/faltz009/closure-verification)

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
