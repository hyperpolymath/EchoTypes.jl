# EchoTypes.jl — wiki

**Executable finite-domain companion** to the Agda library
[hyperpolymath/echo-types](https://github.com/hyperpolymath/echo-types).
Each callable is the finite shadow of a named Agda lemma; the
Agda is the proof, the Julia is the lab.

> The package is **NOT a proof**. Julia has no proof checker. The
> test suite exhibits each theorem on concrete finite data; a green
> test does not promote the claim to a theorem of the underlying
> domain. The Agda module the test points to does.

## Quick links

- **Source**: [src/EchoTypes.jl](https://github.com/hyperpolymath/EchoTypes.jl/blob/main/src/EchoTypes.jl)
- **Tests**: [test/runtests.jl](https://github.com/hyperpolymath/EchoTypes.jl/blob/main/test/runtests.jl)
- **README + lookup table**: [README.md](https://github.com/hyperpolymath/EchoTypes.jl/blob/main/README.md)
- **Upstream Agda**: [hyperpolymath/echo-types](https://github.com/hyperpolymath/echo-types)
- **Upstream wiki — Julia companion exercises** (mirror of
  [[Exercises]] on this side):
  [echo-types/wiki/Julia-Companion-Exercises](https://github.com/hyperpolymath/echo-types/wiki/Julia-Companion-Exercises)

## Pages

- [[Exercises]] — 10 hands-on exercises with REPL transcripts
  bridging each EchoTypes.jl callable back to its Agda lemma.
- [[Honest-Bound-Discipline]] — what the package's matched-negative
  blocks pin, what they don't, and the category errors to avoid.
- [[Adding-A-New-Shadow]] — submission guide for proposing a
  finite shadow of an unmirrored Agda lemma.

## Current pin

`v0.3.0` mirrors echo-types `origin/main` at
`eed42503a1a4c54ec0a347ebef3440b4d4db30c9` (2026-05-28). The
package's preamble carries the SoT pin; re-pin a fresh clone if
you want to track HEAD.

## Coverage map (one-line summary)

| Tier | Modules shadowed | Julia testsets |
|---|---|---|
| Foundation (v0.1.0) | Echo / EchoResidue / EchoFiberCount / EchoThermodynamics | 6 |
| Canonical identity (v0.2.0) | TotalCompletion / OFS / Image / NoSectionGeneric / LossTaxonomy / Entropy / ObsEquivalence | 7 |
| Audience-facing + LL gap (v0.3.0) | Provenance / Security / ProbabilisticSupport / Differential / LLEncoding | 5 |
| **Total** | **15 Agda modules** | **18 testsets, 253 passing assertions** |

## Intentionally NOT mirrored

The package's scope is **K-free + decidable + finite-witness**. The
following surfaces are out by policy:

- **Funext-qualified** — F5-1/2/3 strict surfaces, F4 pullback
  strict UP. Julia has no funext to take as hypothesis.
- **R-2026-05-18 retracted** — graded-comonad framing, universal
  property, conservativity, two-models. The mechanised laws survive
  upstream under different framings; the retracted *surface* is not
  reproduced here.
- **HoTT-strength** — UIP, propositional truncation, HITs. The
  proof-relevant *upper* of each pair is what lands; the truncated
  *lower* (e.g., (epi, mono) image) needs a HIT carrier and is not
  Julia-shadowable.
- **Ordinal-lane** — Slice 3/4 umbrella, `RankPow*`, head-Ω
  inversion, joint-bplus scaffolds. Separate pillar; a Julia shadow
  would require a new `Bord` carrier and explicit scope agreement
  before being added.

See the README for the full carve-out rationale.

## License

`MPL-2.0` (legal fallback until PMPL is formally recognised). The
LICENSE file, README declaration, and every source SPDX header
agree — one consistent licence, deliberately not a Project-vs-source
split.
