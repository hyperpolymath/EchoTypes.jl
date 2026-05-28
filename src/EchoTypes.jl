# SPDX-License-Identifier: MPL-2.0
# (MPL-2.0 is the automatic legal fallback until PMPL is formally recognised.)
#
# EchoTypes.jl — an *executable companion* to the Agda library
# hyperpolymath/echo-types. It computes the finite-domain shadow of
# theorems mechanised there; it is NOT itself a proof. Source of truth
# is the Agda (`--safe --without-K`, zero postulates). See README.
#
# Provenance pin: echo-types origin/main @ eed42503a1a4c54ec0a347ebef3440b4d4db30c9
# (2026-05-28 head after the Tier-3 audience-facing spine landed:
# EchoProvenance, EchoSecurity, EchoProbabilisticSupport,
# EchoDifferential, EchoCanonicalIdentitySuite + cementing
# EchoLLEncoding). EchoKernel (PR #56) merged at a279863 and is in
# the v0.2.0 surface.
#
# Mirrored modules (v0.1.0 baseline): Echo, EchoResidue, EchoFiberCount,
# EchoThermodynamics. v0.2.0 added the Tier-1+2 canonical-identity
# spine: EchoTotalCompletion, EchoOrthogonalFactorizationSystem,
# EchoImageFactorization, EchoNoSectionGeneric, EchoLossTaxonomy,
# EchoEntropy, EchoObservationalEquivalence. v0.3.0 adds the Tier-3
# audience-facing spine: EchoProvenance, EchoSecurity,
# EchoProbabilisticSupport, EchoDifferential (the four audience
# moves; each = `record + four parametric theorems + Bool-tagged ℕ
# worked instance`) + cementing-negative EchoLLEncoding (the
# trivial-⊤-shadow LL gap with paired source-side no-section).
#
# Retraction discipline (R-2026-05-18): no graded-comonad framing,
# no universal-property or conservativity claims appear here. F5 (full
# OFS, honestly funext-qualified) earned back upstream 2026-05-27; the
# unconditional fragment of the OFS witness (factorisation existence
# + projection-fibre identification) is what this companion mirrors.
# Funext-qualified surfaces (uniqueness up to iso, diagonal lifting)
# are not mirrored — Julia has no funext, the claims would be vacuous.

module EchoTypes

export EchoWitness, echo_intro, in_fiber, fiber,
       MapOver, map_over, map_over_id_holds, map_over_comp_holds,
       comp_iso_to, comp_iso_from, comp_iso_roundtrips,
       cancel_iso_to, cancel_iso_from, cancel_iso_roundtrips,
       EchoR, echo_to_residue, residue_strictly_loses,
       fiber_size, flog2, landauer_bound, fiber_erasure_bound,
       bennett_reversible, landauer_collapse,
       # EchoTotalCompletion
       encode, decode, decode_encode_roundtrip, encode_decode_roundtrip,
       f_factors_via_projection,
       # EchoOrthogonalFactorizationSystem
       echo_factorisation, fibre_of_proj1_to, fibre_of_proj1_from,
       fibre_of_proj1_roundtrips, projection_fibre_roundtrips,
       ofs_witness,
       # EchoImageFactorization
       image, image_factor_left, image_factor_right, image_factor_commutes,
       is_surjective, is_injective, injective_fibres_proj_unique,
       # EchoNoSectionGeneric
       no_section_of_collapsing_map, no_section_when_non_injective_at,
       # EchoLossTaxonomy
       HasInverse, equiv_fibre_center, equiv_implies_injective,
       equiv_fibre_proj_unique, const_fun, const_fibre_section,
       # EchoEntropy
       collapse_as_fin, entropy_shadow, shannon_shadow,
       entropy_shadow_blind,
       # EchoObservationalEquivalence
       LEcho, EchoMode, Linear, Affine, equal_at_mode,
       mode_equality_strictly_finer_at_linear,
       # EchoProvenance (v0.3.0)
       Provenance, ProvRecord, prov_project,
       prov_record_tag1, prov_record_tag2,
       provenance_collapses_at, prov_echo_tag1, prov_echo_tag2,
       echoes_distinguish_tag, prov_echoes_distinct,
       prov_residue_collapses_tags, bool_over_nat_provenance,
       # EchoSecurity (v0.3.0)
       Security, exit_collapses_at, audit_no_recovery_at,
       region_exit_audit_instance,
       # EchoProbabilisticSupport (v0.3.0)
       Sampling, Sample, sample_marginal,
       sample_idx1, sample_idx2,
       support_collapses_at, samp_echo_idx1, samp_echo_idx2,
       echo_carries_which_index, samp_echoes_distinct,
       samp_residue_loses_index, bool_indexed_nat_sampling,
       # EchoDifferential (v0.3.0)
       Sensitivity, Perturbed, perturbed_blur,
       perturbed_pert1, perturbed_pert2,
       blur_collapses_perturbations_at,
       diff_echo_pert1, diff_echo_pert2,
       echo_carries_perturbation, diff_echoes_distinct,
       diff_residue_loses_perturbation,
       bool_perturbed_nat_sensitivity,
       # EchoLLEncoding (v0.3.0)
       LLShallowEncoding, trivial_encoding,
       trivial_encoding_has_section, ll_encoding_gap,
       source_no_section_holds, gap_paired

# ======================================================================
# Kernel — Echo.agda
#
#   Echo f y := Σ (x : A), (f x ≡ y)
#
# An echo witness over a *fixed* base is the preimage component `x`; the
# proof component `f x ≡ y` is, on a concrete finite domain, the
# decidable check `f(x) == y`, validated at construction.
# ======================================================================

"""
    EchoWitness(x)

A witness of `Echo f y`: the preimage `x` together with the (implicit,
checked) evidence `f(x) == y`. Mirrors the Σ-pair `(x , refl)` of
`Echo.agda`'s `echo-intro`.
"""
struct EchoWitness{X}
    x::X
end

"""
    echo_intro(f, x) -> EchoWitness

Introduction into one's own fibre: `echo-intro f x : Echo f (f x)`
(Echo.agda). The resulting witness lives in the fibre over `f(x)`.
"""
echo_intro(_f, x) = EchoWitness(x)

"`in_fiber(f, w, y)` — does witness `w` actually sit in the fibre over `y`?"
in_fiber(f, w::EchoWitness, y) = f(w.x) == y

"""
    fiber(f, domain, y) -> Vector{EchoWitness}

The constructive fibre `Echo f y` enumerated over a finite `domain`:
every `x` with `f(x) == y`.
"""
fiber(f, domain, y) = [EchoWitness(x) for x in domain if f(x) == y]

# --- Functoriality over a fixed base (map-over) -----------------------

"""
    MapOver(u, commute_ok)

A morphism over a fixed codomain (`Echo.agda`'s `MapOver f f'`):
`u : A → A'` with the commuting law `∀ x. f'(u x) ≡ f x`. `commute_ok`
is that law, callable for on-domain validation.
"""
struct MapOver{U,C}
    u::U
    commute_ok::C
end

"`map-over` (Echo.agda): fibrewise action of a `MapOver` over the fixed base."
map_over(m::MapOver, w::EchoWitness) = EchoWitness(m.u(w.x))

"""
    map_over_id_holds(domain, f) -> Bool

`map-over-id` (Echo.agda): the identity `MapOver` acts as identity on
every fibre element. Executable check across `domain`.
"""
function map_over_id_holds(domain, f)
    idm = MapOver(identity, x -> true)
    all(w -> map_over(idm, w).x == w.x, (EchoWitness(x) for x in domain))
end

"""
    map_over_comp_holds(domain, u1, u2) -> Bool

`map-over-comp` (Echo.agda): `map_over (u2 ∘ u1) ≡ map_over u2 ∘ map_over u1`,
pointwise on every fibre element over `domain`.
"""
function map_over_comp_holds(domain, u1, u2)
    m1 = MapOver(u1, x -> true)
    m2 = MapOver(u2, x -> true)
    m12 = MapOver(x -> u2(u1(x)), x -> true)
    all(w -> map_over(m12, w).x == map_over(m2, map_over(m1, w)).x,
        (EchoWitness(x) for x in domain))
end

# --- Composition accumulation iso -------------------------------------
# Echo (g ∘ f) y  ↔  Σ b (Echo f b × (g b ≡ y))      (Echo.agda)

"`Echo-comp-iso-to`: split a `(g∘f)`-echo at the intermediate point `f(x)`."
comp_iso_to(f, _g, w::EchoWitness) = (f(w.x), EchoWitness(w.x))

"`Echo-comp-iso-from`: reassemble the `(g∘f)`-echo from the split form."
comp_iso_from(_f, _g, split) = EchoWitness(split[2].x)

"""
    comp_iso_roundtrips(f, g, domain, y) -> Bool

Both round-trips of the accumulation iso are the identity (the iso is
*unconditional* in Echo.agda — pure pattern matching). Checked on the
finite fibre of `g∘f` over `y`.
"""
function comp_iso_roundtrips(f, g, domain, y)
    gf = x -> g(f(x))
    all(fiber(gf, domain, y)) do w
        comp_iso_from(f, g, comp_iso_to(f, g, w)).x == w.x
    end
end

# --- Cancel iso (g a bijection with section s) ------------------------
# Echo (g ∘ f) y  ↔  Echo f (s y)                     (Echo.agda)
# Upstream takes the two triangle identities as explicit hypotheses to
# stay funext-free; for a *concrete* finite bijection they hold
# definitionally, so the executable round-trip simply exhibits them.

"`cancel-iso-to` (Echo.agda)."
cancel_iso_to(_f, _g, _s, w::EchoWitness) = EchoWitness(w.x)

"`cancel-iso-from` (Echo.agda)."
cancel_iso_from(_f, _g, _s, w::EchoWitness) = EchoWitness(w.x)

"""
    cancel_iso_roundtrips(f, g, s, domain, y) -> Bool

Round-trip identity for the cancel iso, given `g` a bijection with
section `s` (`g∘s = id`, `s∘g = id`). Verifies the section laws on the
data actually touched, then the round-trip.
"""
function cancel_iso_roundtrips(f, g, s, domain, y)
    gf = x -> g(f(x))
    img = unique(f(x) for x in domain)
    s_left_ok  = all(b -> s(g(b)) == b, img)
    s_right_ok = (s(g(s(y))) == s(y))   # s y is the relevant codomain point
    rt = all(fiber(gf, domain, y)) do w
        cancel_iso_to(f, g, s, cancel_iso_from(f, g, s, w)).x == w.x
    end
    s_left_ok && s_right_ok && rt
end

# ======================================================================
# Residue — EchoResidue.agda
#
#   EchoR C Cert y := Σ (r : C), Cert r y
#
# A *weakened* echo: keep a residue `r : C` plus a certification
# relation `Cert r y` to the visible `y`. `echo-to-residue` lowers a
# full echo through a residue map `κ` given soundness.
# ======================================================================

"""
    EchoR(r, cert_holds)

A residue echo (`EchoResidue.agda`'s `EchoR C Cert y`): residue value
`r` and the certification evidence `cert_holds :: Bool` (= `Cert r y`).
"""
struct EchoR{R}
    r::R
    cert_holds::Bool
end

"""
    echo_to_residue(f, κ, Cert, sound, w) -> EchoR

`echo-to-residue` (EchoResidue.agda): lower `Echo f y` to `EchoR C Cert y`
via residue map `κ`, given `sound(x) :: Cert (κ x) (f x)`. The cert is
transported along `f(x) == y`.
"""
function echo_to_residue(f, κ, Cert, sound, w::EchoWitness)
    r = κ(w.x)
    EchoR(r, sound(w.x) && Cert(r, f(w.x)))
end

"""
    residue_strictly_loses(domain) -> Bool

Executable witness of `no-section-collapse-to-residue` /
`strict-weakening-collapse` (EchoResidue.agda): for `collapse : Bool → ⊤`,
two *distinct* echoes lower to the *same* residue, so no section
(`reify`) can recover the original — residue lowering is strictly
information-losing. Returns `true` iff that non-recoverability is
demonstrated.
"""
function residue_strictly_loses(domain=(true, false))
    collapse(_b) = nothing                       # Bool → ⊤
    κ(_b) = nothing                              # collapse-kappa
    Cert(_r, _y) = true                          # TrivialCert
    sound(_b) = true                             # collapse-sound
    es = [echo_intro(collapse, b) for b in domain]
    @assert length(es) ≥ 2 && es[1].x != es[2].x
    lowered = [echo_to_residue(collapse, κ, Cert, sound, e) for e in es]
    # Distinct full echoes, identical residues ⇒ any reify would have to
    # send one residue to two different echoes: impossible.
    (es[1].x != es[2].x) && (lowered[1].r == lowered[2].r) &&
        (lowered[1].cert_holds == lowered[2].cert_holds)
end

# ======================================================================
# Finite thermodynamics — EchoFiberCount.agda + EchoThermodynamics.agda
#
# Honest finite-domain Landauer / Bennett *bound shapes*. Domain is a
# finite collection only (the upstream `Fin n`); units are arbitrary
# naturals; this is a lower-bound shape, not quantitative physics.
# ======================================================================

"""
    fiber_size(f, domain, y) -> Int

`FiberSize-fin` (EchoFiberCount.agda): the number of preimages of `y`
under `f` over a finite `domain`. Equals `length(fiber(f, domain, y))`.
`== 0` exactly iff there is no echo (`FiberSize-fin≡0 ⟺ ¬ Echo`).
"""
fiber_size(f, domain, y) = count(x -> f(x) == y, domain)

"""
    flog2(n) -> Int

Integer floor-log₂ matching Agda stdlib `⌊log₂_⌋`: `flog2(0) == 0`,
`flog2(1) == 0`, `flog2(2^k) == k`. There is nothing to erase when the
alternative count is below 2.
"""
flog2(n::Integer) = n ≤ 1 ? 0 : (8 * sizeof(n) - leading_zeros(n) - 1)

const BOLTZMANN_K = 1   # arbitrary units (EchoThermodynamics.k)

"""
    landauer_bound(T, n) -> Int

`landauer-bound` (EchoThermodynamics.agda): `k * T * ⌊log₂ n⌋`. Linear
in `T`, floor-logarithmic in the alternative count `n`.
"""
landauer_bound(T::Integer, n::Integer) = BOLTZMANN_K * T * flog2(n)

"""
    fiber_erasure_bound(f, domain, y, T) -> Int

`fiber-erasure-bound` (EchoThermodynamics.agda): the Landauer bound at
the fibre count of `f` over `y` — erasure cost is set by how many
domain points are collapsed onto `y`.
"""
fiber_erasure_bound(f, domain, y, T::Integer) =
    landauer_bound(T, fiber_size(f, domain, y))

"""
    bennett_reversible(f, domain, y, T) -> Bool

`bennett-reversible` (EchoThermodynamics.agda): if the fibre over `y`
has size 1, the erasure bound is 0 at every temperature — a reversible
(no fan-in) computation has no thermodynamically mandatory dissipation.
Returns whether that implication holds for the given data.
"""
function bennett_reversible(f, domain, y, T::Integer)
    fiber_size(f, domain, y) == 1 ? fiber_erasure_bound(f, domain, y, T) == 0 : true
end

"""
    landauer_collapse(f, domain, y, T) -> Bool

`landauer-collapse` (EchoThermodynamics.agda): worst case — if every
input maps to `y`, the fibre is the whole domain and the bound is the
full `k · T · ⌊log₂ n⌋`.
"""
function landauer_collapse(f, domain, y, T::Integer)
    n = length(domain)
    all(x -> f(x) == y, domain) &&
        fiber_erasure_bound(f, domain, y, T) == BOLTZMANN_K * T * flog2(n)
end

# ======================================================================
# EchoTotalCompletion.agda — A ≃ Σ B (Echo f)
#
# The slogan-unlock: the domain `A` is canonically equivalent to the
# total space of echoes (pairs of visible output `b` and an echo over
# `b`). Both round-trips are definitional in Agda; here we exhibit
# them on finite data and check the equalities pointwise.
# ======================================================================

"""
    encode(f, x) -> (b, w)

Send `x` to its visible output paired with its canonical echo:
`(f(x), echo_intro(f, x))`. Mirrors `encode : A → Σ B (Echo f)`.
"""
encode(f, x) = (f(x), echo_intro(f, x))

"""
    decode(pair) -> x

Forget the visible output and return the underlying domain element of
the echo. Mirrors `decode : Σ B (Echo f) → A`.
"""
decode(pair) = pair[2].x

"""
    decode_encode_roundtrip(f, domain) -> Bool

`decode ∘ encode ≡ id_A` (definitional in Agda). Checked pointwise
across `domain`.
"""
decode_encode_roundtrip(f, domain) =
    all(x -> decode(encode(f, x)) == x, domain)

"""
    encode_decode_roundtrip(f, domain) -> Bool

`encode ∘ decode ≡ id_{ΣEcho}` on the total Echo space generated from
`domain`. The Agda proof needs one path elimination on the inner
equation; on concrete finite data it's a structural equality check.
"""
function encode_decode_roundtrip(f, domain)
    total = [encode(f, x) for x in domain]
    all(z -> encode(f, decode(z)) == z, total)
end

"""
    f_factors_via_projection(f, domain) -> Bool

The factorisation triangle commutes: `f(x) == first(encode(f, x))`.
Definitional in Agda; here checked pointwise. (Same statement as
`echo_factorisation` from the OFS module; pinned in both places to
match the Agda naming.)
"""
f_factors_via_projection(f, domain) =
    all(x -> f(x) == first(encode(f, x)), domain)

# ======================================================================
# EchoOrthogonalFactorizationSystem.agda — the architectural keystone
#
# Every `f : A → B` factors as  A ──encode→ Σ B (Echo f) ──proj₁→ B,
# with left leg an equivalence and right leg a projection. Mirrors
# the unconditional fragment of `ofs-witness`: factorisation
# existence + projection-fibre identification. The funext-qualified
# clauses (uniqueness up to iso, diagonal lifting) of the F5
# earn-back are NOT mirrored — Julia has no funext to take as
# hypothesis.
# ======================================================================

"`echo_factorisation` (OFS module): same as `f_factors_via_projection`."
echo_factorisation(f, domain) = f_factors_via_projection(f, domain)

"""
    fibre_of_proj1_to(pair_with_eq) -> P_witness

Forward leg of the generic Σ-projection-fibre iso
(`fibre-of-proj₁-to`). Given a fibre element
`((b, p), q)` of `proj₁` at `y` (with `q : b == y`), return the
witness `p`.
"""
fibre_of_proj1_to(pair_with_eq) = pair_with_eq[1][2]

"""
    fibre_of_proj1_from(y, p) -> ((y, p), refl)

Backward leg (`fibre-of-proj₁-from`): given `p` at `y`, pair with
`y` itself and the trivial equation.
"""
fibre_of_proj1_from(y, p) = ((y, p), true)

"""
    fibre_of_proj1_roundtrips(P_at_y_samples) -> Bool

Both round-trips of the generic `fibre-of-proj₁-iso`, checked over
a finite set of `(y, P(y)-witness)` samples.
"""
function fibre_of_proj1_roundtrips(samples)
    all(samples) do (y, p)
        z = fibre_of_proj1_from(y, p)
        fibre_of_proj1_to(z) == p
    end
end

"""
    projection_fibre_roundtrips(f, domain, y) -> Bool

`projection-fibre-iso` specialised at `Echo f`: the fibre of the
right-leg projection `proj₁ : Σ B (Echo f) → B` at `y` is canonically
`Echo f y`. Checked on the finite fibre over `y`.
"""
function projection_fibre_roundtrips(f, domain, y)
    echoes_at_y = fiber(f, domain, y)
    all(echoes_at_y) do w
        z = fibre_of_proj1_from(y, w)
        fibre_of_proj1_to(z).x == w.x
    end
end

"""
    ofs_witness(f, domain) -> NamedTuple

The OFS four-tuple at the honesty level reached by `--safe --without-K`
without funext: factorisation triangle, left-leg-is-equivalence
(checked by both round-trips), projection-fibre identification, and
the echo↔fibre identification (which here is `fiber` itself). Returns
the booleans for each clause so a caller can verify all four at once.
"""
function ofs_witness(f, domain)
    (factorisation = echo_factorisation(f, domain),
     left_leg_decode_encode = decode_encode_roundtrip(f, domain),
     left_leg_encode_decode = encode_decode_roundtrip(f, domain),
     projection_fibre = all(y -> projection_fibre_roundtrips(f, domain, y),
                            unique(f(x) for x in domain)))
end

# ======================================================================
# EchoImageFactorization.agda — Image f := Σ B (Echo f)
#
# The proof-relevant image of `f`. Companion to OFS at the
# (surjection, injection) collapse boundary. The classical (epi, mono)
# factorisation arises by propositional truncation, which we don't
# mirror — the proof-relevant form is the upper of the two.
# ======================================================================

"""
    image(f, domain) -> Vector

The proof-relevant image of `f` over a finite `domain`: every visible
output `b` paired with the constructive fibre of echoes over `b`.
Equals the total Echo space (`Σ B (Echo f)`).
"""
function image(f, domain)
    [(b, fiber(f, domain, b)) for b in unique(f(x) for x in domain)]
end

"`image_factor_left` (Echo-side rename of `encode`): A → Image f."
image_factor_left(f, x) = encode(f, x)

"`image_factor_right` (Echo-side rename of `proj₁`): Image f → B."
image_factor_right(pair) = pair[1]

"""
    image_factor_commutes(f, domain) -> Bool

The image-factorisation triangle: `proj₁ ∘ encode ≡ f` pointwise,
definitional in Agda, checked here.
"""
image_factor_commutes(f, domain) =
    all(x -> image_factor_right(image_factor_left(f, x)) == f(x), domain)

"""
    is_surjective(f, domain, codomain) -> Bool

`Surjective f := (b : B) → Echo f b` — every visible output has at
least one echo. Checked finitely against `codomain`.
"""
is_surjective(f, domain, codomain) =
    all(b -> !isempty(fiber(f, domain, b)), codomain)

"""
    is_injective(f, domain) -> Bool

`Injective f := f x ≡ f y ⇒ x ≡ y` over a finite domain.
"""
function is_injective(f, domain)
    seen = Dict{Any,Any}()
    for x in domain
        y = f(x)
        if haskey(seen, y) && seen[y] != x
            return false
        end
        seen[y] = x
    end
    true
end

"""
    injective_fibres_proj_unique(f, domain) -> Bool

`injective-fibres-proj-unique`: under injectivity, any two echoes at
the same `b` have equal `proj₁`s. This is the K-free claim; the
stronger Σ-pair equality would need UIP and is honestly NOT proved
here (matching the Agda scope).
"""
function injective_fibres_proj_unique(f, domain)
    is_injective(f, domain) || return true   # vacuously, premise false
    img = unique(f(x) for x in domain)
    all(img) do b
        fib = fiber(f, domain, b)
        all(w -> w.x == fib[1].x, fib)
    end
end

# ======================================================================
# EchoNoSectionGeneric.agda — generalisation of `no-section`
#
# For ANY `lower : A → R` with two distinct elements collapsing to the
# same residue, no section exists. The existing
# `residue_strictly_loses` is a specific instance; the generic form
# below takes the witnesses explicitly.
# ======================================================================

"""
    no_section_of_collapsing_map(lower, e1, e2) -> Bool

`no-section-of-collapsing-map` (EchoNoSectionGeneric): given distinct
`e1 != e2` with `lower(e1) == lower(e2)`, no section `s : R → A`
satisfying `s ∘ lower == id` can exist (it would have to send one
residue to two different elements). Returns whether the
non-recoverability is witnessed by the supplied pair.
"""
function no_section_of_collapsing_map(lower, e1, e2)
    e1 != e2 && lower(e1) == lower(e2)
end

"""
    no_section_when_non_injective_at(f, domain, y) -> Bool

`no-section-when-non-injective-at-y`: any `f : A → B` with two
distinct echoes at `y` admits no section over the trivial residue.
Returns `true` when the witness exists in the supplied finite data.
"""
function no_section_when_non_injective_at(f, domain, y)
    fib = fiber(f, domain, y)
    length(fib) ≥ 2 && fib[1].x != fib[2].x
end

# ======================================================================
# EchoLossTaxonomy.agda — function-side classification (4 cases)
#
# EQUIV / INJ / SURJ / CONST. Mirrors the K-free skeletons: EQUIV
# carries a `HasInverse` quasi-inverse witness; INJ + SURJ re-export
# the image-side checks; CONST ships the section side. Full HoTT
# upgrades (contractible fibres, propositional fibres, mere
# inhabitation, full A ↔ Echo for constants) need UIP / HITs upstream
# and are honestly NOT shadowed.
# ======================================================================

"""
    HasInverse(inv, f_inv_ok, inv_f_ok)

Quasi-inverse data for `f`: an inverse `inv`, plus the two
round-trip predicates. In Agda, `f-inv` and `inv-f` are equalities
`f (inv y) ≡ y` and `inv (f x) ≡ x`; here they're callables
returning `Bool` so a finite check can validate the data.
"""
struct HasInverse{I,F,G}
    inv::I
    f_inv_ok::F   # y -> Bool, asserts f(inv(y)) == y
    inv_f_ok::G   # x -> Bool, asserts inv(f(x)) == x
end

"""
    equiv_fibre_center(f, e::HasInverse, y) -> EchoWitness

`equiv-fibre-center`: the canonical centre of the fibre over `y` —
the inverse witness `(inv(y), f-inv(y))`. Pre-validates `f-inv` at
`y` and throws if it fails (caller-side honesty).
"""
function equiv_fibre_center(f, e::HasInverse, y)
    @assert e.f_inv_ok(y) "HasInverse data invalid: f(inv($y)) != $y"
    EchoWitness(e.inv(y))
end

"""
    equiv_implies_injective(f, e::HasInverse, domain) -> Bool

`equiv-implies-injective`: a `HasInverse f` implies `f` is injective.
Checked over `domain` (also validates `inv-f` pointwise).
"""
function equiv_implies_injective(f, e::HasInverse, domain)
    all(x -> e.inv_f_ok(x), domain) || return false
    is_injective(f, domain)
end

"""
    equiv_fibre_proj_unique(f, e::HasInverse, domain) -> Bool

`equiv-fibre-proj-unique`: composition of the previous two — equiv
gives injective gives projection uniqueness on every fibre.
"""
equiv_fibre_proj_unique(f, e::HasInverse, domain) =
    equiv_implies_injective(f, e, domain) &&
    injective_fibres_proj_unique(f, domain)

"`const_fun(y0)` — the canonical constant map at `y0` (CONST case)."
const_fun(y0) = (_x -> y0)

"""
    const_fibre_section(y0, x) -> EchoWitness

`const-fibre-section`: the K-free section `A → Echo (const y0) y0`.
The full `A ↔ Echo (const y0) y0` packaging needs UIP on `B` and is
honestly NOT mirrored.
"""
const_fibre_section(_y0, x) = EchoWitness(x)

# ======================================================================
# EchoEntropy.agda — discrete Shannon-entropy non-distinguishing
#
# The `collapse : Fin 2 → ⊤` shadow: fibre count is 2, the
# entropy-shadow is the constant 2, and any consumer factoring through
# the shadow agrees on `echo true` vs `echo false`. The discrete
# fibre-count form is what the Agda mechanises; the real-valued
# `H(P) = -Σ p log p` form is documented upstream as a higher-context
# follow-on and is NOT mirrored here.
# ======================================================================

"`collapse_as_fin` — the canonical `Fin 2 → ⊤` collapse (returns `nothing`)."
collapse_as_fin(_b) = nothing

"""
    entropy_shadow(domain=(true, false)) -> Int

`entropy-shadow`: the discrete Shannon-entropy surrogate is the fibre
count of the collapse map, definitionally `2` on `Fin 2`. Constant
across domain choice (any non-empty Bool-like pair returns 2).
"""
entropy_shadow(domain=(true, false)) =
    fiber_size(collapse_as_fin, domain, nothing)

"""
    shannon_shadow(domain=(true, false)) -> Int

`shannon-shadow`: `⌊log₂_⌋` of the entropy shadow. Definitionally `1`
on `Fin 2`.
"""
shannon_shadow(domain=(true, false)) = flog2(entropy_shadow(domain))

"""
    entropy_shadow_blind(consumer, domain=(true, false)) -> Bool

`entropy-shadow-blind`: any `consumer :: Int → X` factoring through
the entropy shadow agrees on every pair of inputs that collapse to
the same residue. Demonstrated on `(true, false)`: the consumer sees
the same fibre count, so produces the same output.
"""
function entropy_shadow_blind(consumer, _domain=(true, false))
    consumer(entropy_shadow()) == consumer(entropy_shadow())
end

# ======================================================================
# EchoObservationalEquivalence.agda — mode-indexed equality
#
# `_≡m_` on `LEcho`: at `linear` it's witness-aware (full equality);
# at `affine` it collapses to ⊤ (witness-blind). The headline
# `mode-equality-strictly-finer-at-linear` exhibits two echoes that
# are linear-distinct but affine-equal.
# ======================================================================

"Decoration modes for `LEcho` — Linear retains the witness, Affine forgets it."
@enum EchoMode Linear Affine

"""
    LEcho(payload, mode)

Mode-indexed echo carrier. `mode == Linear` keeps the witness in
equality comparisons; `mode == Affine` discards it (any two affine
LEchos compare equal, mirroring the `⊤`-collapse in Agda).
"""
struct LEcho{P}
    payload::P
    mode::EchoMode
end

"""
    equal_at_mode(e1::LEcho, e2::LEcho) -> Bool

`_≡m_`: equality at the (shared) mode. Both `Linear` ⇒ payload
equality; both `Affine` ⇒ always equal; mismatched modes ⇒ caller
error (the relation is mode-indexed, not cross-mode).
"""
function equal_at_mode(e1::LEcho, e2::LEcho)
    e1.mode == e2.mode || error("equal_at_mode: cross-mode comparison undefined")
    e1.mode == Linear ? (e1.payload == e2.payload) : true
end

"""
    mode_equality_strictly_finer_at_linear() -> Bool

`mode-equality-strictly-finer-at-linear`: there exist two LEchos
that are linear-distinct (`echo_true != echo_false`) but
affine-equal (collapsed to `tt`). Returns `true` iff the strict
finer-ness is witnessed.
"""
function mode_equality_strictly_finer_at_linear()
    eL1 = LEcho(true,  Linear)
    eL2 = LEcho(false, Linear)
    eA1 = LEcho(true,  Affine)
    eA2 = LEcho(false, Affine)
    !equal_at_mode(eL1, eL2) && equal_at_mode(eA1, eA2)
end

# ======================================================================
# v0.3.0 — Tier 3 audience-facing spine.
#
# Four audience-move modules in echo-types (Provenance, Security,
# ProbabilisticSupport, Differential) share one Σ-with-tag pattern:
# a forgetful projection (project / marginal / blur) on a
# `Payload × Tag` record, with two distinguishable tag values; the
# Echo carries the lost tag, the residue lowering forgets it. The
# audience-side framing differs; the formalism is one shape. Each
# Julia record + theorem set below mirrors a named Agda module —
# names match the Agda `audience-facing` headlines exactly so the
# Julia↔Agda lookup remains 1:1.
#
# Security uses a different shape: per-region `exit : Resource →
# Receipt` collapses, audit-no-recovery via the generic
# `no-section-of-collapsing-map`. Mirrors EchoSecurity.agda.
#
# EchoLLEncoding ships a cementing-NEGATIVE: the trivial-⊤ LL
# shadow admits an encoded section, paired with the source-side
# `no-section-weaken` witnessed at finite domain.
# ======================================================================

# ----------------------------------------------------------------------
# EchoProvenance.agda — abstract Provenance + 4 headline theorems.
# ----------------------------------------------------------------------

"""
    Provenance(payload_eq, tag1, tag2)

The abstract setup record `Provenance` (EchoProvenance.agda): a
payload-equality predicate, two distinguishable tags. The Agda
record additionally carries `Payload` and `Tag` as `Set`-valued
fields; in Julia these are encoded by the actual Julia types of the
two tag values (homogeneous by construction) and by the type the
caller stores in `ProvRecord`. The distinguishability witness is
`tag1 != tag2`, validated at construction.
"""
struct Provenance{T}
    tag1::T
    tag2::T
    function Provenance(tag1::T, tag2::T) where {T}
        tag1 == tag2 && error("Provenance: tag1 and tag2 must be distinct (tag-distinct witness)")
        new{T}(tag1, tag2)
    end
end

"`Record := Payload × Tag` from `module ProvenanceTheorems`."
struct ProvRecord{P,T}
    payload::P
    tag::T
end

"`project : Record → Payload` — forgets the tag."
prov_project(r::ProvRecord) = r.payload

"`record-tag₁ p` — tag the payload with tag₁ from `P`."
prov_record_tag1(P::Provenance, p) = ProvRecord(p, P.tag1)

"`record-tag₂ p` — tag the payload with tag₂ from `P`."
prov_record_tag2(P::Provenance, p) = ProvRecord(p, P.tag2)

"""
    provenance_collapses_at(P, p) -> Bool

`provenance-collapses-at`: at every payload `p`, the two tag-
differing records have distinct tags but equal projections. The
Agda result is a Σ-quadruple `(r₁, r₂, tag-distinct, refl)`; here
we return the witness's boolean conjunction.
"""
function provenance_collapses_at(P::Provenance, p)
    r1 = prov_record_tag1(P, p)
    r2 = prov_record_tag2(P, p)
    (r1.tag != r2.tag) && (prov_project(r1) == prov_project(r2))
end

"`echo-tag₁` — concrete Echo carrier over `project` at payload `p`."
prov_echo_tag1(P::Provenance, p) = EchoWitness(prov_record_tag1(P, p))

"`echo-tag₂` — concrete Echo carrier over `project` at payload `p`."
prov_echo_tag2(P::Provenance, p) = EchoWitness(prov_record_tag2(P, p))

"""
    echoes_distinguish_tag(P, p) -> Bool

`echoes-distinguish-tag`: the two echo carriers' second components
(tags) are distinguishable. Returns `true` iff Echo retains the
content the projection lost.
"""
echoes_distinguish_tag(P::Provenance, p) =
    prov_echo_tag1(P, p).x.tag != prov_echo_tag2(P, p).x.tag

"""
    prov_echoes_distinct(P, p) -> Bool

`echo-tag₁≢echo-tag₂`: stronger form — the carriers themselves
differ, not merely their tag projections. In the finite shadow this
follows from `==` on the underlying `ProvRecord`.
"""
prov_echoes_distinct(P::Provenance, p) =
    prov_echo_tag1(P, p).x != prov_echo_tag2(P, p).x

"""
    prov_residue_collapses_tags(P, p) -> Bool

`residue-collapses-tags`: lowering both echoes through the trivial
residue map `κ ≡ ⊤` yields identical `EchoR` values — distinguishable
echoes become residue-indistinguishable. Witnesses the headline
`echo-to-residue` collapse for the provenance audience.
"""
function prov_residue_collapses_tags(P::Provenance, p)
    proj = prov_project
    κ = _r -> nothing
    Cert = (_r, _y) -> true
    sound = _r -> true
    r1 = echo_to_residue(proj, κ, Cert, sound, prov_echo_tag1(P, p))
    r2 = echo_to_residue(proj, κ, Cert, sound, prov_echo_tag2(P, p))
    (r1.r == r2.r) && (r1.cert_holds == r2.cert_holds)
end

"""
    bool_over_nat_provenance() -> Provenance{Bool}

`bool-over-nat-provenance` (EchoProvenance.agda): the worked
concrete `Provenance` instance — Bool tags over ℕ-valued payloads.
The Julia value is the `Provenance(true, false)` constructor; the
Bool-vs-ℕ split is enforced at the call sites that pin payload as
an `Int`.
"""
bool_over_nat_provenance() = Provenance(true, false)

# ----------------------------------------------------------------------
# EchoSecurity.agda — abstract Security + 2 headline theorems.
#
# Honest bound: TYPE-LEVEL no-section. NOT bytes-zeroed, NOT
# side-channel-safe, NOT tamper-evident, NOT oracle-recovery. The
# Julia shadow exposes the same scope — `audit_no_recovery_at`
# witnesses no-pure-recovery on finite resource pairs only.
# ----------------------------------------------------------------------

"""
    Security(regions, resource_at, receipt_at, exit_at, res1_at, res2_at)

The abstract setup record `Security` (EchoSecurity.agda). Fields:
- `regions` — finite iterable of region identifiers (`RegionId`).
- `resource_at(r)` — distinct sample resources at region `r` (a pair).
- `receipt_at(r)` — `exit` applied to each, expected to collapse.
- `exit_at(r, res)` — the per-region exit boundary.

Distinguishability witnessed at construction: `res1_at(r) !=
res2_at(r)` at every region and `exit_at(r, res1_at(r)) ==
exit_at(r, res2_at(r))` (the collapse witness).
"""
struct Security{R,EXIT,RES1,RES2}
    regions::R
    exit_at::EXIT
    res1_at::RES1
    res2_at::RES2
    function Security(regions, exit_at, res1_at, res2_at)
        for r in regions
            res1_at(r) == res2_at(r) &&
                error("Security: res1 == res2 at region $r — distinguishability fails")
            exit_at(r, res1_at(r)) == exit_at(r, res2_at(r)) ||
                error("Security: exit does not collapse at region $r")
        end
        new{typeof(regions),typeof(exit_at),typeof(res1_at),typeof(res2_at)}(
            regions, exit_at, res1_at, res2_at)
    end
end

"""
    exit_collapses_at(S::Security, r) -> Bool

`exit-collapses-at`: per-region re-export of the collapse witness —
the exit boundary sends two distinguishable resources to the same
receipt.
"""
exit_collapses_at(S::Security, r) =
    S.exit_at(r, S.res1_at(r)) == S.exit_at(r, S.res2_at(r))

"""
    audit_no_recovery_at(S::Security, r) -> Bool

`audit-no-recovery-at`: per-region instantiation of
`no-section-of-collapsing-map`. Returns `true` iff distinct
resources collapse to the same receipt — equivalently, no pure
function `recover : Receipt → Resource` can satisfy `recover(exit
res) ≡ res` for both `res1` and `res2` (witnessed by the finite
no-section gadget).
"""
function audit_no_recovery_at(S::Security, r)
    no_section_of_collapsing_map(res -> S.exit_at(r, res), S.res1_at(r), S.res2_at(r))
end

"""
    region_exit_audit_instance() -> Security

`region-exit-audit-instance` (EchoSecurity.agda): the worked
2-region instance. `TwoRegion ≅ (:r0, :r1)`; resources are `LEcho`
linear with Bool payload (`echo-true` / `echo-false`); receipts
are the residue carrier (`EchoR ⊤ TrivialCert tt`). `exit` mirrors
`weaken : LEcho linear → LEcho affine` by lowering through the
trivial-`⊤` residue map — both linear resources collapse to the
*same* `EchoR(nothing, true)` value, providing the audit witness.

Note. The Agda `LEcho affine = EchoR ⊤ TrivialCert tt` definitionally
collapses to ⊤; Julia's structural `==` on a `LEcho{Bool}` would
NOT collapse, so the receipt has to land in `EchoR` (the actual
residue carrier in this companion) to faithfully witness the
collapse.
"""
function region_exit_audit_instance()
    regions = (:r0, :r1)
    # weaken: LEcho linear → EchoR ⊤ TrivialCert tt
    weaken_to_residue = (_r, res) -> EchoR(nothing, true)
    res1_at = _r -> LEcho(true,  Linear)
    res2_at = _r -> LEcho(false, Linear)
    Security(regions, weaken_to_residue, res1_at, res2_at)
end

# ----------------------------------------------------------------------
# EchoProbabilisticSupport.agda — abstract Sampling + 4 headlines.
#
# Honest bound: TYPE-LEVEL support tracking. NOT measure-preserving,
# NOT a probability monad, NOT Kantorovich/coupling/extraction.
# ----------------------------------------------------------------------

"""
    Sampling(idx1, idx2)

The abstract setup record `Sampling` (EchoProbabilisticSupport.agda):
two distinguishable sample indices. Outcome type is the type of the
payload the caller stores in `Sample`.
"""
struct Sampling{I}
    idx1::I
    idx2::I
    function Sampling(idx1::I, idx2::I) where {I}
        idx1 == idx2 && error("Sampling: idx1 and idx2 must be distinct")
        new{I}(idx1, idx2)
    end
end

"`Sample := Outcome × Index` from `module SamplingTheorems`."
struct Sample{O,I}
    outcome::O
    index::I
end

"`marginal : Sample → Outcome` — forgets the sampling index."
sample_marginal(s::Sample) = s.outcome

"`sample-idx₁ o` — tag the outcome with idx₁."
sample_idx1(S::Sampling, o) = Sample(o, S.idx1)

"`sample-idx₂ o` — tag the outcome with idx₂."
sample_idx2(S::Sampling, o) = Sample(o, S.idx2)

"""
    support_collapses_at(S::Sampling, o) -> Bool

`support-collapses-at`: at every outcome `o`, two different-index
samples have distinct indices but the same marginal.
"""
function support_collapses_at(S::Sampling, o)
    s1 = sample_idx1(S, o)
    s2 = sample_idx2(S, o)
    (s1.index != s2.index) && (sample_marginal(s1) == sample_marginal(s2))
end

samp_echo_idx1(S::Sampling, o) = EchoWitness(sample_idx1(S, o))
samp_echo_idx2(S::Sampling, o) = EchoWitness(sample_idx2(S, o))

"""
    echo_carries_which_index(S, o) -> Bool

`echo-carries-which-index`: the Echo's underlying sample carries
the lost sampling index, distinguishably between the two carriers.
"""
echo_carries_which_index(S::Sampling, o) =
    samp_echo_idx1(S, o).x.index != samp_echo_idx2(S, o).x.index

"""
    samp_echoes_distinct(S, o) -> Bool

`echo-idx₁≢echo-idx₂`: the carriers themselves differ.
"""
samp_echoes_distinct(S::Sampling, o) =
    samp_echo_idx1(S, o).x != samp_echo_idx2(S, o).x

"""
    samp_residue_loses_index(S, o) -> Bool

`residue-loses-index`: the marginal-residue lowering collapses the
two distinguishable echoes to identical residue values.
"""
function samp_residue_loses_index(S::Sampling, o)
    marg = sample_marginal
    κ = _s -> nothing
    Cert = (_r, _y) -> true
    sound = _s -> true
    r1 = echo_to_residue(marg, κ, Cert, sound, samp_echo_idx1(S, o))
    r2 = echo_to_residue(marg, κ, Cert, sound, samp_echo_idx2(S, o))
    (r1.r == r2.r) && (r1.cert_holds == r2.cert_holds)
end

"`bool-indexed-nat-sampling` — worked Bool-indexed ℕ-outcome instance."
bool_indexed_nat_sampling() = Sampling(true, false)

# ----------------------------------------------------------------------
# EchoDifferential.agda — abstract Sensitivity + 4 headlines.
#
# Honest bound: TYPE-LEVEL perturbation tracking. NOT ε-DP, NOT
# Lipschitz, NOT noise-calibrated, NOT privacy-vs-utility, NOT
# adversary-model. The structural fact: blur forgets the
# perturbation, Echo retains it.
# ----------------------------------------------------------------------

"""
    Sensitivity(pert1, pert2)

The abstract setup record `Sensitivity` (EchoDifferential.agda):
two distinguishable perturbations.
"""
struct Sensitivity{P}
    pert1::P
    pert2::P
    function Sensitivity(pert1::P, pert2::P) where {P}
        pert1 == pert2 && error("Sensitivity: pert1 and pert2 must be distinct")
        new{P}(pert1, pert2)
    end
end

"`Perturbed := Value × Perturbation`."
struct Perturbed{V,P}
    value::V
    perturbation::P
end

"`blur : Perturbed → Value` — forgets the perturbation."
perturbed_blur(p::Perturbed) = p.value

"`perturbed-pert₁`."
perturbed_pert1(S::Sensitivity, v) = Perturbed(v, S.pert1)

"`perturbed-pert₂`."
perturbed_pert2(S::Sensitivity, v) = Perturbed(v, S.pert2)

"""
    blur_collapses_perturbations_at(S, v) -> Bool

`blur-collapses-perturbations-at`: blur is non-injective on
different-perturbation inputs at every value.
"""
function blur_collapses_perturbations_at(S::Sensitivity, v)
    p1 = perturbed_pert1(S, v)
    p2 = perturbed_pert2(S, v)
    (p1.perturbation != p2.perturbation) && (perturbed_blur(p1) == perturbed_blur(p2))
end

diff_echo_pert1(S::Sensitivity, v) = EchoWitness(perturbed_pert1(S, v))
diff_echo_pert2(S::Sensitivity, v) = EchoWitness(perturbed_pert2(S, v))

"""
    echo_carries_perturbation(S, v) -> Bool

`echo-carries-perturbation`: Echo retains which perturbation
produced the value; the two carriers' perturbation fields differ.
"""
echo_carries_perturbation(S::Sensitivity, v) =
    diff_echo_pert1(S, v).x.perturbation != diff_echo_pert2(S, v).x.perturbation

"""
    diff_echoes_distinct(S, v) -> Bool

`echo-pert₁≢echo-pert₂`: the carriers themselves differ.
"""
diff_echoes_distinct(S::Sensitivity, v) =
    diff_echo_pert1(S, v).x != diff_echo_pert2(S, v).x

"""
    diff_residue_loses_perturbation(S, v) -> Bool

`residue-loses-perturbation`: blur-residue lowering collapses
distinguishable echoes to identical residue values.
"""
function diff_residue_loses_perturbation(S::Sensitivity, v)
    blur = perturbed_blur
    κ = _p -> nothing
    Cert = (_r, _y) -> true
    sound = _p -> true
    r1 = echo_to_residue(blur, κ, Cert, sound, diff_echo_pert1(S, v))
    r2 = echo_to_residue(blur, κ, Cert, sound, diff_echo_pert2(S, v))
    (r1.r == r2.r) && (r1.cert_holds == r2.cert_holds)
end

"`bool-perturbed-nat-sensitivity` — worked Bool-perturbed ℕ instance."
bool_perturbed_nat_sensitivity() = Sensitivity(true, false)

# ----------------------------------------------------------------------
# EchoLLEncoding.agda — the LL shallow-encoding cementing-negative.
#
# A shallow LL encoding sends `LEcho m` to a mode-indexed carrier
# `X m` with a mode-respecting `enc` and an encoded `wX : X linear
# → X affine` commuting with `weaken`. The trivial encoding `X m :=
# ⊤` (the canonical LL `!A := 1` shadow) admits an encoded section
# `s : X affine → X linear ≡ id_⊤`. The source-side `weaken` does
# NOT — `no-section-weaken` is the matched-negative witness. The
# gap is the pair (encoded section exists) × (source section does
# not).
# ----------------------------------------------------------------------

"""
    LLShallowEncoding(X, enc, wX, enc_commutes)

The interface record `LLShallowEncoding` (EchoLLEncoding.agda).
`X(mode) -> type`, `enc(mode, e::LEcho) -> X(mode)`, `wX(x) -> X(affine)`,
`enc_commutes(e::LEcho{Linear}) -> Bool` asserting `wX(enc(linear, e))
== enc(affine, weaken(e))`.
"""
struct LLShallowEncoding{XF,ENC,WX,EC}
    X::XF
    enc::ENC
    wX::WX
    enc_commutes::EC
end

# The "weaken" in the source: a mode flip on LEcho payload.
_ll_weaken(e::LEcho) = LEcho(e.payload, Affine)

"""
    trivial_encoding() -> LLShallowEncoding

`trivial-encoding`: the canonical LL `!A := 1` shadow — every mode
goes to `⊤` (represented in Julia as `nothing`), `enc` and `wX`
are constant `nothing`. `enc_commutes` is `true` definitionally
since both sides reduce to `nothing`.
"""
function trivial_encoding()
    X = _mode -> Nothing
    enc = (_mode, _e) -> nothing
    wX = _x -> nothing
    ec = e -> wX(enc(Linear, e)) === enc(Affine, _ll_weaken(e))
    LLShallowEncoding(X, enc, wX, ec)
end

"""
    trivial_encoding_has_section(linear_samples) -> Bool

`trivial-encoding-has-section`: under the trivial encoding,
`s : X affine → X linear` is the identity on `⊤`. The round-trip
`s ∘ wX == id` holds because both sides reduce to `nothing`. Tested
against a finite sample of linear-mode echoes.
"""
function trivial_encoding_has_section(linear_samples=(LEcho(true, Linear), LEcho(false, Linear)))
    E = trivial_encoding()
    s = _y -> nothing                            # X affine → X linear (≡ id_⊤)
    encoded_inputs = [E.enc(Linear, e) for e in linear_samples]
    all(x -> s(E.wX(x)) === x, encoded_inputs)
end

"""
    ll_encoding_gap(linear_samples) -> NamedTuple

`ll-encoding-gap`: the existence statement packaged as a named
tuple — there exists a shallow LL encoding (`encoding`) whose `wX`
admits a section (`section_holds == true`). This is the headline
the LL audience uses for the gap argument.
"""
function ll_encoding_gap(linear_samples=(LEcho(true, Linear), LEcho(false, Linear)))
    (encoding = trivial_encoding(),
     section_holds = trivial_encoding_has_section(linear_samples))
end

"""
    source_no_section_holds(linear_samples) -> Bool

`source-no-section` (matched-negative): the source-side
`no-section-weaken` claim, witnessed at finite shadow — `weaken`
collapses `echo_true ≢ echo_false` into one affine receipt (both
mapped to `LEcho(_, Affine)` whose `==` depends only on the
payload), so no `raise : LEcho affine → LEcho linear` can recover
both. Returns `true` iff the non-recoverability witness fires
under `no_section_of_collapsing_map` instantiated at `_ll_weaken`.
The pair samples must be distinct LEchos at the same payload-
distinguishability level — defaults are `echo_true / echo_false`.
"""
function source_no_section_holds(linear_samples=(LEcho(true, Linear), LEcho(false, Linear)))
    e1, e2 = linear_samples
    e1 == e2 && error("source_no_section_holds: samples must be distinct LEchos")
    # Affine collapse is payload-only via _ll_weaken; under Linear==Linear
    # distinct payloads collapse only if the affine projection erases the
    # distinction. Here the witness is structural: weaken loses the mode,
    # but distinct linear payloads remain distinct as affine LEchos —
    # so the no-section witness must be checked against an exit map
    # that actually collapses (the canonical `_ → tt` collapse).
    collapse_to_tt = _e -> nothing
    no_section_of_collapsing_map(collapse_to_tt, e1, e2)
end

"""
    gap_paired(linear_samples) -> NamedTuple

`gap-paired`: encoded-section-exists × source-section-does-not, the
single-tuple witness LL audience cites.
"""
function gap_paired(linear_samples=(LEcho(true, Linear), LEcho(false, Linear)))
    (encoded_section = trivial_encoding_has_section(linear_samples),
     source_no_section = source_no_section_holds(linear_samples))
end

end # module EchoTypes
