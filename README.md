<!-- SPDX-License-Identifier: PMPL-1.0-or-later -->
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
`origin/main` commit `2ca31220e3efdcf2708e6d2e04869993fbb1e53a`:

| Julia surface | Mirrors Agda module / lemmas |
|---|---|
| `EchoWitness`, `echo_intro`, `fiber`, `map_over*`, `comp_iso_*`, `cancel_iso_*` | `Echo.agda` (kernel; the funext-free core, see `EchoKernel`) |
| `EchoR`, `echo_to_residue`, `residue_strictly_loses` | `EchoResidue.agda` (`echo-to-residue`, `strict-weakening-collapse`) |
| `fiber_size`, `flog2`, `landauer_bound`, `fiber_erasure_bound`, `bennett_reversible`, `landauer_collapse` | `EchoFiberCount.agda` + `EchoThermodynamics.agda` |

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

`v0.1.0`, local development. **Not registered** in the Julia General
registry and intentionally **not** part of the
AcceleratorGate→KnotTheory→Skein→KRLAdapter registration chain — it is
a standalone companion, registered only on its own merit if and when
that is warranted.

## Licence

`PMPL-1.0-or-later`; `MPL-2.0` (see [`LICENSE`](LICENSE)) is the
automatic legal fallback until PMPL is formally recognised. The
LICENSE file, this statement, and every source SPDX header agree —
one consistent licence, deliberately not a Project-vs-source split.
