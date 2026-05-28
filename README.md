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
`origin/main` commit `eed42503a1a4c54ec0a347ebef3440b4d4db30c9`
(2026-05-28 head, after the Tier-3 audience-facing spine landed —
EchoProvenance, EchoSecurity, EchoProbabilisticSupport,
EchoDifferential, EchoLLEncoding, plus the
EchoCanonicalIdentitySuite re-export bundle):

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
| **v0.3.0** `Provenance`, `ProvRecord`, `provenance_collapses_at`, `prov_echo_tag1/2`, `echoes_distinguish_tag`, `prov_residue_collapses_tags`, `bool_over_nat_provenance` | `EchoProvenance.agda` (Tier-3 audience move 1 — 4 parametric theorems + Bool-over-ℕ instance) |
| **v0.3.0** `Security`, `exit_collapses_at`, `audit_no_recovery_at`, `region_exit_audit_instance` | `EchoSecurity.agda` (Tier-3 audience move 2 — per-region audit no-recovery via the generic no-section gadget) |
| **v0.3.0** `Sampling`, `Sample`, `support_collapses_at`, `samp_echo_idx1/2`, `echo_carries_which_index`, `samp_residue_loses_index`, `bool_indexed_nat_sampling` | `EchoProbabilisticSupport.agda` (Tier-3 audience move 3 — marginal loses sampling index) |
| **v0.3.0** `Sensitivity`, `Perturbed`, `blur_collapses_perturbations_at`, `diff_echo_pert1/2`, `echo_carries_perturbation`, `diff_residue_loses_perturbation`, `bool_perturbed_nat_sensitivity` | `EchoDifferential.agda` (Tier-3 audience move 4 — blur loses perturbation tag) |
| **v0.3.0** `LLShallowEncoding`, `trivial_encoding`, `trivial_encoding_has_section`, `ll_encoding_gap`, `source_no_section_holds`, `gap_paired` | `EchoLLEncoding.agda` (cementing-negative — the LL `!A := 1` shadow admits an encoded section paired with source-side no-section) |

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

- **Ordinal-lane work (`Ordinal/Buchholz/*`).** The Slice-3 + Slice-4
  rank-mono umbrella, `RankPow*`, head-Ω inversion, joint-bplus
  scaffolds — all live in echo-types's ordinal pillar, separate
  from the echo functor / residue / thermodynamics core this
  companion mirrors. Adding ordinal shadows would require a new
  `Bord` carrier in Julia and a redesigned scope agreement. Not
  in v0.3.0; out-of-scope for the companion's stated discipline.

### Honest-bound discipline (Tier 3)

The four v0.3.0 audience-facing modules ship explicit "what is
NOT proved" lists upstream — `EchoSecurity` is type-level
no-section, NOT bytes-zeroed / side-channel-safe / tamper-evident;
`EchoProbabilisticSupport` is support tracking, NOT measure
theory / coupling / extraction; `EchoDifferential` is perturbation
tracking, NOT ε-DP / Lipschitz / noise calibration. The Julia
testsets preserve this scope in their comments. Consumers should
not promote a green test to a real-world security or privacy
claim — those need additional structure beyond the finite shadow.

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

`v0.3.0`, local development. The v0.1.0 surface (`Echo`,
`EchoResidue`, `EchoFiberCount`, `EchoThermodynamics`) and the
v0.2.0 Tier-1+Tier-2 canonical-identity spine are preserved
unchanged; v0.3.0 adds executable shadows of the Tier-3
audience-facing spine that landed upstream on 2026-05-27/28
(`EchoProvenance`, `EchoSecurity`, `EchoProbabilisticSupport`,
`EchoDifferential`) plus the cementing-negative `EchoLLEncoding`
(LL shallow-encoding gap with paired source-side no-section).
Test suite: **253 passing assertions across 18 testsets**, each
the finite shadow of a named Agda lemma. Registered as
`EchoTypes` in the hyperpolymath professional registry; **not**
registered in the Julia General registry and intentionally **not**
part of the AcceleratorGate→KnotTheory→Skein→KRLAdapter chain — it
is a standalone companion.

## Licence

`MPL-2.0`; `MPL-2.0` (see [`LICENSE`](LICENSE)) is the
automatic legal fallback until PMPL is formally recognised. The
LICENSE file, this statement, and every source SPDX header agree —
one consistent licence, deliberately not a Project-vs-source split.
