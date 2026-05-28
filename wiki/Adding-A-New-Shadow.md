# Adding a new shadow — submission guide

This guide is for PRs that add a finite shadow of an
echo-types Agda lemma not yet mirrored.

## The bar

Every Julia callable in the package satisfies four invariants. A
new shadow must too:

1. **Named.** It corresponds to a specific Agda module + theorem.
   Cite both in the docstring.
2. **Finite-witness-checkable.** The decision procedure terminates
   on concrete finite data; no infinitary state, no funext, no
   UIP.
3. **K-free.** The Agda module sits under `--safe --without-K`
   with zero postulates. (Check the upstream module's first line +
   `tools/check-guardrails.sh` clean status.)
4. **Honest-bound documented.** Any matched-negative scope from
   the upstream module is preserved in the testset comments.

## What is OUT of scope

These shadow-types are explicitly NOT accepted, even with a
careful implementation:

- **Funext-qualified surfaces** — F5 strict / pullback strict / F4
  template anything taking `funext` as a hypothesis. Julia has no
  funext primitive; the conditional becomes vacuous.
- **R-2026-05-18 retracted framings** — graded-comonad, universal
  property, conservativity, two-models. The mechanised laws survive
  upstream under other framings; the retracted *surface* is closed
  by policy.
- **HoTT-strength** — UIP-requiring claims (full Σ-pair equality
  under injectivity, contractible fibres), propositional
  truncation (the (epi, mono) image), HITs.
- **Ordinal-lane work** — Slice 3/4 umbrella, `RankPow*`,
  head-Ω inversion, joint-bplus scaffolds. Separate pillar; would
  require a new `Bord` carrier in Julia and an explicit scope
  agreement before being added. File a discussion first if you
  want to pursue this direction.

## PR checklist

The PR description must include:

- [ ] **Agda module + theorem name** the shadow corresponds to.
- [ ] **Finite-shadow-suitability argument** — one sentence on
  why this lemma admits a witness-checkable finite form.
- [ ] **Matched-negative block** — what does your test NOT
  witness? (Even if the upstream module is silent, list the
  obvious non-claims a casual reader might infer.)
- [ ] **Testset added** with at least one passing assertion per
  named theorem clause.
- [ ] **README lookup-table row** added under the appropriate
  version section.
- [ ] **SoT pin updated** if the upstream commit you're tracking is
  newer than the current pin in `src/EchoTypes.jl`'s preamble.

## Suggested template

```julia
# ----------------------------------------------------------------------
# <UpstreamModule>.agda — short description.
#
# Honest scope: <one-line of what's IN>. Out-of-scope per upstream
# matched-negative block: <one-line of what's NOT>.
# ----------------------------------------------------------------------

"""
    <julia_callable>(args) -> Bool

`<agda-theorem-name>` (`<UpstreamModule>.agda`): one-line of what
the theorem says. The finite-shadow check returns `true` iff the
witness fires at the supplied data.
"""
function <julia_callable>(args)
    # finite computation matching the Agda theorem statement.
end
```

And the testset:

```julia
@testset "<UpstreamModule>: <theorem name>" begin
    # HONEST BOUND: <one-line scope reminder>.

    @test <julia_callable>(<simple-input>)

    # Construction validators fire on misuse.
    @test_throws ErrorException <julia_callable>(<deliberately-bad-input>)
end
```

## Review process

Reviews focus on three things:

1. **Does the Agda upstream actually prove what the docstring
   claims?** Reviewers will open the Agda module and read the
   named theorem. If the docstring drifts from the Agda, the PR
   is fixed before merge.
2. **Is the finite shadow faithful?** A shadow that passes for
   the wrong reason (e.g., because the test uses an empty
   collection) is rejected.
3. **Is the matched-negative block accurate?** If the upstream
   module pins explicit non-claims, the PR's testset comments
   must reproduce them.

## Examples to study

Existing well-shaped shadows that you can use as templates:

- **Single-headline + worked instance**: `EchoEntropy` / `entropy_shadow`
- **Abstract record + parametric theorems**: `EchoProvenance` /
  `Provenance` + `provenance_collapses_at`
- **No-section pattern**: `EchoNoSectionGeneric` /
  `no_section_of_collapsing_map`
- **Round-trip identity**: `EchoTotalCompletion` /
  `decode_encode_roundtrip`
- **Existence / matched-negative pair**: `EchoLLEncoding` /
  `gap_paired`

## Where to ask

- Repo discussions: https://github.com/hyperpolymath/EchoTypes.jl/discussions
- Upstream-side wiki:
  [echo-types/wiki/Julia-Companion-Exercises](https://github.com/hyperpolymath/echo-types/wiki/Julia-Companion-Exercises)
- Open an issue if a lemma sits at a scope boundary (HoTT-strength,
  funext-qualified) and you want a ruling before opening a PR.
