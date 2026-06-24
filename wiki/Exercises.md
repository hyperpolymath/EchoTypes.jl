<!--
SPDX-License-Identifier: CC-BY-SA-4.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Exercises — hands-on EchoTypes.jl ↔ echo-types

These exercises walk through each Julia callable + the Agda lemma
it shadows, with a REPL transcript and an extend-this prompt.

This page is the **EchoTypes.jl side** of the bridge; the
upstream-side mirror lives at
[echo-types/wiki/Julia-Companion-Exercises](https://github.com/hyperpolymath/echo-types/wiki/Julia-Companion-Exercises).
Both pages contain the same 10 exercises, presented from each
repo's perspective — pick whichever entry point matches your
current focus.

> **Honesty discipline.** Julia has no proof checker. A green test
> only *exhibits* the lemma at a finite shadow. If a Julia test
> fails on your data, the input may be wrong *or* the lemma might
> not apply under the encoding used — chase the divergence; don't
> reach for the proof until you're sure of the finite witness.

---

## Setup

```julia
julia> using Pkg

julia> Pkg.add(url="https://github.com/hyperpolymath/EchoTypes.jl")

julia> using EchoTypes
```

The package is **not** in Julia's General registry. It carries its
own SoT pin tying v0.3.0 to echo-types `eed4250` (2026-05-28).

---

## Exercise 1 — Echo kernel (`Echo.agda`)

The foundation. `Echo f y := Σ (x : A), (f x ≡ y)` — the echo over
`y` is the fibre of `f` at `y`.

**Agda:** [`Echo.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/Echo.agda)
| **Julia:** `EchoWitness`, `echo_intro`, `fiber`,
`comp_iso_roundtrips`, `cancel_iso_roundtrips`.

```julia
julia> f = x -> x % 3;  dom = 0:11;

julia> fiber(f, dom, 1)
4-element Vector{EchoWitness{Int64}}:   #  x = 1, 4, 7, 10

julia> in_fiber(f, echo_intro(f, 7), 1)
true

julia> comp_iso_roundtrips(x -> x % 4, b -> b % 2, 0:15, 1)
true
```

**Extend.** Define `g : 0:15 → 0:5`. Print `fiber(g, 0:15, y)` for
some `y`. Prove on paper why the length matches `FiberSize-fin` —
this is the definitional identity in disguise.

---

## Exercise 2 — Residue weakening (`EchoResidue.agda`)

Lower a full echo to a residue; show two distinct echoes can
collapse, witnessing no-section.

**Agda:** [`EchoResidue.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoResidue.agda)
| **Julia:** `echo_to_residue`, `residue_strictly_loses`,
`no_section_of_collapsing_map`.

```julia
julia> residue_strictly_loses((true, false))
true

julia> no_section_of_collapsing_map(_ -> nothing, :a, :b)
true
```

**Extend.** Pick `κ : 0:9 → 0:2`. Find `n₁ ≠ n₂` with
`κ(n₁) == κ(n₂)`. Run `no_section_of_collapsing_map(κ, n₁, n₂)`.
What goes wrong with `n₁ == n₂`? Map this to the Agda
`trans/sym/cong` proof structure.

---

## Exercise 3 — Total completion (`EchoTotalCompletion.agda`)

The slogan unlock: `A ≃ Σ B (Echo f)`. Every irreversible map's
domain is canonically equivalent to its total echo space.

**Agda:** [`EchoTotalCompletion.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoTotalCompletion.agda)
| **Julia:** `encode`, `decode`, `decode_encode_roundtrip`,
`encode_decode_roundtrip`, `f_factors_via_projection`.

```julia
julia> f = x -> x % 4;
julia> encode(f, 7)
(3, EchoTypes.EchoWitness{Int64}(7))

julia> decode_encode_roundtrip(f, 0:11)
true

julia> encode_decode_roundtrip(f, 0:11)
true
```

**Extend.** Pick a `parity`-shaped `f`. Compute the disjoint union
of `Bool × Echo f true` and `Bool × Echo f false` from `encode`.
Where does the lost parity bit live in the encoding?

---

## Exercise 4 — Orthogonal factorisation system (`EchoOrthogonalFactorizationSystem.agda`)

The architectural keystone:
`A ─encode→ Σ B (Echo f) ─proj₁→ B`. Honest scope = unconditional
fragment only.

**Agda:** [`EchoOrthogonalFactorizationSystem.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoOrthogonalFactorizationSystem.agda)
| **Julia:** `ofs_witness`.

```julia
julia> ofs_witness(x -> x % 3, 0:8)
(factorisation = true, left_leg_decode_encode = true,
 left_leg_encode_decode = true, projection_fibre = true)
```

**Extend.** Construct an `f, dom` pair that breaks one clause
(hint: pick a `dom` that doesn't cover the codomain Julia thinks
of). Trace which clause flips. Why does the Agda statement quantify
over the actual image to avoid this?

---

## Exercise 5 — Loss taxonomy + image factorisation

Classify `f` by echo shape (EQUIV / INJ / SURJ / CONST), K-free
skeletons only.

**Agda:** [`EchoLossTaxonomy.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoLossTaxonomy.agda)
+ [`EchoImageFactorization.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoImageFactorization.agda)
| **Julia:** `HasInverse`, `equiv_implies_injective`,
`equiv_fibre_center`, `is_surjective`, `is_injective`, `image`.

```julia
julia> g = x -> (x + 1) % 5; g_inv = y -> (y + 4) % 5;
julia> e = HasInverse(g_inv, y -> g(g_inv(y)) == y,
                              x -> g_inv(g(x)) == x);
julia> equiv_implies_injective(g, e, 0:4)
true

julia> equiv_fibre_center(g, e, 2)
EchoTypes.EchoWitness{Int64}(1)        # g(1) == 2 ✓
```

**Extend.** Predict + check `is_surjective(_ -> 42, 0:5, 0:5)`.
Read the CONST case companion-remark — why is the full
`A ↔ Echo(const y0)` not mirrored? (UIP on `B`, which the upstream
discipline forbids.)

---

## Exercise 6 — Tier-3 audience moves: Provenance

Database / pipeline / data-engineering audience-facing
generalisation of the existing example into an abstract record.

**Agda:** [`EchoProvenance.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoProvenance.agda)
| **Julia:** `Provenance`, `provenance_collapses_at`,
`prov_echo_tag1/2`, `echoes_distinguish_tag`,
`prov_residue_collapses_tags`, `bool_over_nat_provenance`.

```julia
julia> P = bool_over_nat_provenance()
EchoTypes.Provenance{Bool}(true, false)

julia> all(p -> provenance_collapses_at(P, p), 0:9)
true

julia> e1 = prov_echo_tag1(P, 7); e2 = prov_echo_tag2(P, 7);
julia> (e1.x.tag, e2.x.tag)
(true, false)

julia> prov_residue_collapses_tags(P, 7)
true
```

**Extend.** Define `P2 = Provenance(:client, :server)`. Run the
same headlines. Does anything beyond the symbol names change?
(No — the record is genuinely parametric in the tag type.)

---

## Exercise 7 — Tier-3 audience moves: Security

Per-region exit / capability-flow audit, with explicit honest-
bound scope.

**Agda:** [`EchoSecurity.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoSecurity.agda)
| **Julia:** `Security`, `exit_collapses_at`,
`audit_no_recovery_at`, `region_exit_audit_instance`.

```julia
julia> S = region_exit_audit_instance();

julia> [exit_collapses_at(S, r) for r in S.regions]
2-element Vector{Bool}: [true, true]

julia> [audit_no_recovery_at(S, r) for r in S.regions]
2-element Vector{Bool}: [true, true]
```

**Extend.** Define your own 4-region `Security`. Watch the
constructor reject an `exit_at` that doesn't collapse.

**Critical reminder.** A green `audit_no_recovery_at` only
witnesses that no pure function can recover the resource at the
finite shadow. It says NOTHING about runtime memory, side-channel
leaks, or cryptographic adversaries — see the matched-negative
block in `EchoSecurity.agda`.

---

## Exercise 8 — Tier-3 audience moves: Sampling + Differential

Same Σ-with-tag pattern as Provenance, audience-side renames.

**Agda:** [`EchoProbabilisticSupport.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoProbabilisticSupport.agda)
+ [`EchoDifferential.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoDifferential.agda)
| **Julia:** `Sampling`, `Sensitivity`, `support_collapses_at`,
`blur_collapses_perturbations_at`, etc.

```julia
julia> S = bool_indexed_nat_sampling();
julia> support_collapses_at(S, 42)
true

julia> D = bool_perturbed_nat_sensitivity();
julia> blur_collapses_perturbations_at(D, 3)
true
```

**Extend.** This is the audit's most-mistakable surface. List
three real-world claims a casual reader might wrongly attribute
to a green `blur_collapses_perturbations_at` — and the structure
each would need. (Hint: see [[Honest-Bound-Discipline]].)

---

## Exercise 9 — LL-encoding gap (`EchoLLEncoding.agda`)

The cementing-negative: trivial LL `!A := 1` shadow admits an
encoded section despite source-side `weaken` having none.

**Agda:** [`EchoLLEncoding.agda`](https://github.com/hyperpolymath/echo-types/blob/main/proofs/agda/EchoLLEncoding.agda)
| **Julia:** `trivial_encoding`, `ll_encoding_gap`,
`source_no_section_holds`, `gap_paired`.

```julia
julia> trivial_encoding_has_section()
true

julia> source_no_section_holds()
true

julia> gap_paired()
(encoded_section = true, source_no_section = true)
```

**Extend.** Design an `LLShallowEncoding` whose `X linear` retains
payload information. What does `wX` look like? Why is the result
no longer a "shallow LL `!A := 1`" shadow?

---

## Exercise 10 — Build a finite shadow of YOUR favourite lemma

Pick an unmirrored echo-types lemma (the ordinal lane has many;
F5 funext-qualified surfaces are tempting targets). Write the
shadow:

1. State the lemma in plain English.
2. Identify the smallest finite carrier that admits a witness.
3. Write `shadow_of_<lemma>(...) -> Bool`.
4. Add a testset.

Submission guide: [[Adding-A-New-Shadow]].

---

## Where the bridge breaks down

| Upstream surface | Why Julia can't shadow it |
|---|---|
| F5 strict OFS (funext-qualified) | No funext primitive — conditional becomes vacuous |
| Full Σ-pair equality under injectivity | Requires UIP, equivalent to invoking `--with-K` |
| (epi, mono) image factorisation | Needs propositional truncation `∥_∥` |
| Buchholz / Veblen ordinals | Carrier is infinitary; finite `Bord` would need a different design |
| Graded comonad laws (R-2026-05-18 retracted framing) | Out of scope by policy |

These boundaries are honest, not gaps. The package stops where
Julia's strength (run at scale) ends and Agda's strength (prove
once, trust everywhere) begins.
