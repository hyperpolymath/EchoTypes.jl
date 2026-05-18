# SPDX-License-Identifier: PMPL-1.0-or-later
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
end
