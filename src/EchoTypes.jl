# SPDX-License-Identifier: MPL-2.0
# (MPL-2.0 is the automatic legal fallback until PMPL is formally recognised.)
#
# EchoTypes.jl — an *executable companion* to the Agda library
# hyperpolymath/echo-types. It computes the finite-domain shadow of
# theorems mechanised there; it is NOT itself a proof. Source of truth
# is the Agda (`--safe --without-K`, zero postulates). See README.
#
# Provenance pin: echo-types origin/main @ 2ca31220e3efdcf2708e6d2e04869993fbb1e53a
# Mirrored modules: Echo.agda, EchoResidue.agda, EchoFiberCount.agda,
# EchoThermodynamics.agda.
#
# Pending upstream (forward-reference, NOT yet tracked): the curated
# funext-free core EchoKernel.agda is open as echo-types PR #56, not on
# origin/main -- so the pin stays at canonical main and this mirrors
# Echo.agda directly. EchoKernel adds no new mathematics (re-export +
# funext-free certificate); the pin bumps to the squash-merge commit
# when #56 lands. See README "Source of truth".
#
# Retraction R-2026-05-18 honoured: NO graded-comonad /
# universal-property / conservativity surface appears here (those are
# [RETRACTED] under earn-back gates upstream).

module EchoTypes

export EchoWitness, echo_intro, in_fiber, fiber,
       MapOver, map_over, map_over_id_holds, map_over_comp_holds,
       comp_iso_to, comp_iso_from, comp_iso_roundtrips,
       cancel_iso_to, cancel_iso_from, cancel_iso_roundtrips,
       EchoR, echo_to_residue, residue_strictly_loses,
       fiber_size, flog2, landauer_bound, fiber_erasure_bound,
       bennett_reversible, landauer_collapse

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

end # module EchoTypes
