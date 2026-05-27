# SPDX-License-Identifier: MPL-2.0
# (MPL-2.0 is the automatic legal fallback until PMPL is formally recognised.)
#
# Each testset is the finite-domain shadow of a named Agda lemma in
# hyperpolymath/echo-types. The Agda is the proof; these tests only
# confirm the executable mirror behaves as the mechanised statement says.

using EchoTypes
using Test

@testset "EchoTypes.jl — finite shadow of echo-types" begin

    @testset "Kernel: Echo functor (Echo.agda)" begin
        f = x -> x % 3                       # ℤ→ℤ/3, lossy
        dom = 0:11

        # echo-intro lands in its own fibre.
        for x in dom
            @test in_fiber(f, echo_intro(f, x), f(x))
        end

        # fibre = exactly the preimages.
        for y in 0:2
            fib = fiber(f, dom, y)
            @test all(w -> f(w.x) == y, fib)
            @test Set(w.x for w in fib) == Set(x for x in dom if f(x) == y)
        end

        # Functoriality: identity and composition laws (map-over-id,
        # map-over-comp).
        @test map_over_id_holds(dom, f)
        @test map_over_comp_holds(dom, x -> x + 1, x -> 2x)
        @test map_over_comp_holds(dom, x -> x ÷ 2, x -> x % 4)
    end

    @testset "Kernel: composition accumulation iso (Echo.agda)" begin
        f = x -> x % 4
        g = b -> b % 2
        dom = 0:15
        for y in 0:1
            @test comp_iso_roundtrips(f, g, dom, y)
        end
    end

    @testset "Kernel: cancel iso with section (Echo.agda)" begin
        f = x -> x % 5
        g = b -> (b + 1) % 5                 # bijection on ℤ/5
        s = c -> (c + 4) % 5                 # inverse: g∘s = s∘g = id
        dom = 0:24
        for y in 0:4
            @test cancel_iso_roundtrips(f, g, s, dom, y)
        end
    end

    @testset "Residue: EchoR + strict weakening (EchoResidue.agda)" begin
        f = x -> x % 3
        κ = x -> x % 3                       # residue map
        Cert = (r, y) -> r == y              # certification relation
        sound = x -> true
        for x in 0:8
            e = echo_intro(f, x)
            er = echo_to_residue(f, κ, Cert, sound, e)
            @test er.r == κ(x)
            @test er.cert_holds              # sound ∧ Cert(κx, f x)
        end

        # no-section-collapse-to-residue / strict-weakening-collapse:
        # collapse : Bool → ⊤ loses the bit irrecoverably.
        @test residue_strictly_loses((true, false))
    end

    @testset "Finite thermo: fiber count (EchoFiberCount.agda)" begin
        dom = 0:7

        # FiberSize-fin-id-zero: identity has singleton fibres.
        idf = x -> x
        @test all(y -> fiber_size(idf, dom, y) == 1, dom)

        # FiberSize-fin-const: constant map has fibre = |domain|.
        c = _ -> 42
        @test fiber_size(c, dom, 42) == length(dom)

        # FiberSize-fin ≡ 0  ⟺  ¬ Echo.
        @test fiber_size(idf, dom, 999) == 0
        @test isempty(fiber(idf, dom, 999))
        @test fiber_size(idf, dom, 3) > 0
        @test !isempty(fiber(idf, dom, 3))
    end

    @testset "Finite thermo: Landauer/Bennett bound shape (EchoThermodynamics.agda)" begin
        @test flog2(0) == 0
        @test flog2(1) == 0
        @test flog2(2) == 1
        @test flog2(8) == 3
        @test flog2(1024) == 10

        T = 7
        dom = 0:15

        # bennett-reversible: singleton fibre ⇒ zero bound.
        idf = x -> x
        for y in dom
            @test fiber_size(idf, dom, y) == 1
            @test fiber_erasure_bound(idf, dom, y, T) == 0
            @test bennett_reversible(idf, dom, y, T)
        end

        # landauer-collapse: constant map ⇒ full k·T·⌊log₂ n⌋.
        c = _ -> 0
        n = length(dom)
        @test fiber_erasure_bound(c, dom, 0, T) == 1 * T * flog2(n)
        @test landauer_collapse(c, dom, 0, T)
        @test !landauer_collapse(idf, dom, 0, T)   # not a collapse map
    end

    # ------------------------------------------------------------------
    # v0.2.0 additions — Tier 1 + Tier 2 spine from echo-types main
    # @ e7dded6 (2026-05-27). Each testset shadows a named Agda module
    # landed since the v0.1.0 pin (2ca3122).
    # ------------------------------------------------------------------

    @testset "TotalCompletion: A ≃ Σ B (Echo f) (EchoTotalCompletion.agda)" begin
        f = x -> x % 4
        dom = 0:11

        # decode-encode is the identity on A (definitional in Agda).
        @test decode_encode_roundtrip(f, dom)

        # encode-decode is the identity on Σ B (Echo f) (one path elim
        # on the inner equation in Agda; structural here).
        @test encode_decode_roundtrip(f, dom)

        # The factorisation triangle commutes (definitional).
        @test f_factors_via_projection(f, dom)

        # Spot-check: encode then decode an explicit element.
        @test decode(encode(f, 7)) == 7
        @test encode(f, 7) == (3, EchoWitness(7))   # 7 % 4 == 3
    end

    @testset "OFS: factorisation + projection-fibre iso (EchoOrthogonalFactorizationSystem.agda)" begin
        f = x -> x % 3
        dom = 0:8

        @test echo_factorisation(f, dom)

        # Generic Σ-projection-fibre round-trips on synthetic samples.
        samples = [(0, EchoWitness(3)), (1, EchoWitness(4)), (2, EchoWitness(5))]
        @test fibre_of_proj1_roundtrips(samples)

        # Specialised to Echo f at every visible output.
        for y in 0:2
            @test projection_fibre_roundtrips(f, dom, y)
        end

        # The packaged OFS witness — all four clauses hold.
        w = ofs_witness(f, dom)
        @test w.factorisation
        @test w.left_leg_decode_encode
        @test w.left_leg_encode_decode
        @test w.projection_fibre
    end

    @testset "Image factorisation + Surj/Inj (EchoImageFactorization.agda)" begin
        f_lossy = x -> x % 3
        dom = 0:8

        # Image = the proof-relevant total space.
        img = image(f_lossy, dom)
        @test length(img) == 3                    # outputs 0, 1, 2
        @test Set(first.(img)) == Set([0, 1, 2])

        # Triangle commutes.
        @test image_factor_commutes(f_lossy, dom)

        # Surjective onto its actual codomain.
        @test is_surjective(f_lossy, dom, 0:2)
        @test !is_surjective(f_lossy, dom, 0:5)    # 3,4,5 unreachable

        # Injectivity classifier.
        @test is_injective(identity, dom)
        @test !is_injective(f_lossy, dom)

        # K-free projection uniqueness under injectivity.
        @test injective_fibres_proj_unique(identity, dom)
        # For a non-injective f the premise is false, the implication
        # is vacuously true (matches the Agda statement shape).
        @test injective_fibres_proj_unique(f_lossy, dom)
    end

    @testset "Generic no-section (EchoNoSectionGeneric.agda)" begin
        # no-section-of-collapsing-map: distinct elements collapsing
        # to the same residue witness non-recoverability.
        lower = b -> nothing
        @test no_section_of_collapsing_map(lower, true, false)

        # Equal elements do NOT witness collapse (premise false).
        @test !no_section_of_collapsing_map(lower, true, true)

        # Instance: f non-injective at y ⇒ no section.
        f = x -> x % 2
        @test no_section_when_non_injective_at(f, 0:5, 0)
        @test no_section_when_non_injective_at(f, 0:5, 1)
        @test !no_section_when_non_injective_at(identity, 0:5, 3)
    end

    @testset "LossTaxonomy: HasInverse + equiv/inj/surj/const (EchoLossTaxonomy.agda)" begin
        # EQUIV case: g(x) = (x+1) % 5 with inverse g⁻¹(y) = (y+4) % 5
        g     = x -> (x + 1) % 5
        g_inv = y -> (y + 4) % 5
        dom = 0:4
        e = HasInverse(g_inv,
                       y -> g(g_inv(y)) == y,
                       x -> g_inv(g(x)) == x)

        # The fibre centre is the inverse witness.
        for y in dom
            c = equiv_fibre_center(g, e, y)
            @test g(c.x) == y
        end

        @test equiv_implies_injective(g, e, dom)
        @test equiv_fibre_proj_unique(g, e, dom)

        # CONST case: const_fun(42) has section A → Echo (const 42) 42.
        c42 = const_fun(42)
        for x in 0:5
            w = const_fibre_section(42, x)
            @test c42(w.x) == 42
            @test w.x == x
        end
    end

    @testset "Entropy: discrete Shannon shadow (EchoEntropy.agda)" begin
        # collapse_as_fin : Fin 2 → ⊤ ; fibre count is 2.
        @test entropy_shadow() == 2
        @test entropy_shadow((true, false)) == 2

        # ⌊log₂ 2⌋ = 1.
        @test shannon_shadow() == 1

        # entropy-shadow-blind: any consumer factoring through the
        # shadow agrees across collapsed inputs.
        @test entropy_shadow_blind(x -> x * 17)
        @test entropy_shadow_blind(x -> "fib=$x")
    end

    @testset "Observational equivalence: mode-indexed equality (EchoObservationalEquivalence.agda)" begin
        # Same payload, same mode ⇒ equal at any mode.
        @test equal_at_mode(LEcho(1, Linear), LEcho(1, Linear))
        @test equal_at_mode(LEcho(1, Affine), LEcho(1, Affine))

        # Different payload, Linear ⇒ unequal; Affine ⇒ equal (⊤-collapse).
        @test !equal_at_mode(LEcho(1, Linear), LEcho(2, Linear))
        @test equal_at_mode(LEcho(1, Affine), LEcho(2, Affine))

        # The headline strict-finerness witness.
        @test mode_equality_strictly_finer_at_linear()

        # Cross-mode comparisons are deliberately undefined (caller error).
        @test_throws ErrorException equal_at_mode(LEcho(1, Linear),
                                                  LEcho(1, Affine))
    end
end
