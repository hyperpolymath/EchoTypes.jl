<!-- SPDX-License-Identifier: MPL-2.0 -->
<!-- (MPL-2.0 is the automatic legal fallback until PMPL is formally recognised.) -->

# EchoTypes.jl

An **executable companion** to the Agda library
[`hyperpolymath/echo-types`](https://github.com/hyperpolymath/echo-types).

It computes the **finite-domain shadow** of theorems that are
*mechanised* in Agda under `--safe --without-K` with zero postulates.
It lets you *run* the echo / residue / Landauer constructions on
concrete finite data and check their stated laws numerically.

## What this is — and is not

- ✅ **It is** a finite, executable model: enumerate fibres, exercise
  functoriality and the composition/cancel isomorphisms, lower echoes
  to residues, and compute the finite Landauer/Bennett bound shape.
- ❌ **It is not a proof.** Julia has no proof checker. Every guarantee
  lives in the Agda. This package can *falsify* by counterexample but
  it cannot *prove*.
- ❌ **No retracted claims appear here.** Per echo-types
  `docs/retractions.adoc` **R-2026-05-18**, the graded-comonad,
  two-models, universal-property and conservativity framings are
  `[RETRACTED]` and under upstream earn-back gates. None of that
  surface is reproduced here. What *is* here is the post-retraction
  honest core: a loss-graded **reindexing** view (Echo functor +
  functoriality + accumulation iso), the **residue** weakening
  (`EchoR`, with its strict non-recoverability witness), and the
  **finite-domain** Landauer/Bennett *bound shapes*.

## Source of truth

The Agda. This release mirrors `hyperpolymath/echo-types` at
`origin/main` commit `e7dded61bb25b8f86fb6e116f4e2827ca2044bcf`
(2026-05-27 head, after the Tier-1+Tier-2 spine + F5 full-OFS
earn-back + EchoProvenance landed):

| Julia surface | Mirrors Agda module / lemmas |
|---|---|
| `EchoWitness`, `echo_intro`, `fiber`, `map_over*`, `comp_iso_*`, `cancel_iso_*` | `Echo.agda` (kernel — also re-pinned via `EchoKernel.agda` upstream) |
| `EchoR`, `echo_to_residue`, `residue_strictly_loses` | `EchoResidue.agda` (`echo-to-residue`, `strict-weakening-collapse`) |
| `fiber_size`, `flog2`, `landauer_bound`, `fiber_erasure_bound`, `bennett_reversible`, `landauer_collapse` | `EchoFiberCount.agda` + `EchoThermodynamics.agda` |
| **v0.2.0** `encode`, `decode`, `*_roundtrip`, `f_factors_via_projection` | `EchoTotalCompletion.agda` (`A↔ΣEcho`, the slogan-unlock) |
| **v0.2.0** `echo_factorisation`, `fibre_of_proj1_*`, `projection_fibre_roundtrips`, `ofs_witness` | `EchoOrthogonalFactorizationSystem.agda` (factorisation existence + projection-fibre identification — funext-qualified clauses NOT mirrored) |
| **v0.2.0** `image`, `image_factor_*`, `is_surjective`, `is_injective`, `injective_fibres_proj_unique` | `EchoImageFactorization.agda` |
| **v0.2.0** `no_section_of_collapsing_map`, `no_section_when_non_injective_at` | `EchoNoSectionGeneric.agda` |
| **v0.2.0** `HasInverse`, `equiv_fibre_center`, `equiv_implies_injective`, `equiv_fibre_proj_unique`, `const_fun`, `const_fibre_section` | `EchoLossTaxonomy.agda` (4-case classifier — EQUIV/INJ/SURJ/CONST K-free skeletons) |
| **v0.2.0** `collapse_as_fin`, `entropy_shadow`, `shannon_shadow`, `entropy_shadow_blind` | `EchoEntropy.agda` (discrete Shannon shadow) |
| **v0.2.0** `LEcho`, `EchoMode`, `equal_at_mode`, `mode_equality_strictly_finer_at_linear` | `EchoObservationalEquivalence.agda` (mode-indexed equality) |

### What is intentionally NOT mirrored

- **Funext-qualified surfaces.** The F5 earn-back gate gave the full
  OFS (uniqueness up to iso + diagonal lifting) upstream under
  funext, and `EchoPullbackUnivF4` gives the strict pullback
  universal property the same way. Julia has no funext to take as
  hypothesis; the conditional claims would be vacuous. Only the
  unconditional fragment of `ofs-witness` is mirrored.

- **Retracted surface (R-2026-05-18).** Graded-comonad framing,
  two-models, universal-property, conservativity. The mechanised
  laws survive upstream (and so does the model-independence
  theorem), but the *framing* is retracted; the companion does not
  reproduce any of it.

- **Higher type-theoretic structure.** UIP-strength claims
  (full Σ-pair equality under injectivity, `A ↔ Echo(const y0)`,
  contractible fibres), propositional truncation (the
  (epi, mono) collapse of the image factorisation), and HoTT
  identification types beyond decidable equality. The proof-relevant
  *upper* of each pair is what's mirrored, in line with the
  `--safe --without-K` discipline upstream.

Scope limits are inherited honestly: the thermodynamics is a
**finite-domain bound *shape*** in arbitrary natural units — not
quantitative physics, and not defined over infinite state spaces (the
upstream `Fin n` restriction).

## Use

```julia
julia> using EchoTypes

julia> f = x -> x % 3;                 # a lossy map

julia> fiber(f, 0:8, 1)                # the constructive Echo fibre over 1
3-element Vector{EchoWitness{Int64}}:  #  x = 1, 4, 7

julia> fiber_erasure_bound(_ -> 0, 0:15, 0, 7)   # full-collapse Landauer bound
28                                                #  = k·T·⌊log₂ 16⌋ = 1·7·4
```

## Test

```
julia --project=. -e 'using Pkg; Pkg.test()'
```

Every testset is the finite shadow of a named Agda lemma; the suite
must stay green and is the only correctness claim this package makes
about itself.

## Status

`v0.2.0`, local development. The v0.1.0 surface (`Echo`,
`EchoResidue`, `EchoFiberCount`, `EchoThermodynamics`) is preserved
unchanged; v0.2.0 adds executable shadows of the Tier-1+Tier-2
canonical-identity spine that landed upstream on 2026-05-27
(`EchoTotalCompletion`, `EchoOrthogonalFactorizationSystem`,
`EchoImageFactorization`, `EchoNoSectionGeneric`, `EchoLossTaxonomy`,
`EchoEntropy`, `EchoObservationalEquivalence`). Registered as
`EchoTypes` in the hyperpolymath professional registry; **not**
registered in the Julia General registry and intentionally **not**
part of the AcceleratorGate→KnotTheory→Skein→KRLAdapter chain — it
is a standalone companion.

## Licence

`MPL-2.0`; `MPL-2.0` (see [`LICENSE`](LICENSE)) is the
automatic legal fallback until PMPL is formally recognised. The
LICENSE file, this statement, and every source SPDX header agree —
one consistent licence, deliberately not a Project-vs-source split.
