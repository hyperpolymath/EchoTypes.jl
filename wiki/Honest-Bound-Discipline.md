<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# Honest-bound discipline

The package's most-mistakable surfaces are the four Tier-3
audience-facing modules (Provenance / Security / Sampling /
Differential) and the cementing-negative LL-encoding gap. Each
ships an explicit "what is NOT proved" list upstream. This page
collects them in one place + names the category errors to avoid.

## The general rule

> A green Julia test exhibits the lemma at a finite shadow. It
> does NOT promote the lemma to anything stronger than the Agda
> proves. If the Agda's matched-negative block lists a non-claim,
> the Julia test inherits the same non-claim.

When a colleague reads a green test result, ask: "what specific
Agda lemma does this witness?" If the answer is fuzzier than the
Agda module name + a section, you've over-promoted.

---

## EchoSecurity — the type-level / runtime gap

Upstream Agda `EchoSecurity.agda` (the `!! HONEST BOUND, STATED UP
FRONT !!` block) pins:

> This module is a TYPE-LEVEL guarantee that no pure Agda function
> reconstructs a consumed resource from its audit receipt alone.

It is **NOT**:
- `bytes-zeroed` — a runtime claim about memory contents
- `side-channel-safe` — a claim about timing / speculative leaks
- `tamper-evident` — a claim about cryptographic authentication
- `oracle-recovery` — a claim about adversaries with access to
  additional live resources outside the model

**Julia consequence.** `audit_no_recovery_at(S, r) == true` says
exactly: under the finite shadow, no pure recovery function exists.
It says nothing about how the bytes of `resource` are laid out at
runtime, whether the underlying machine zeroises them, what an
adversary with timing access can observe, or whether the receipt
is cryptographically authenticated.

**Category errors to avoid.**
- "We tested `audit_no_recovery_at`, so this protocol is secure."
  (No — security is a runtime property; the test is type-level.)
- "The test passes, so the resource is gone from memory." (No —
  the test says nothing about memory state.)
- "Our adversary cannot recover the resource." (No — the test
  says no *pure function* can; an adversary with oracle access,
  side-channel access, or runtime memory access is outside the
  model.)

---

## EchoProbabilisticSupport — the support / measure gap

Upstream pins:

> It is NOT a measure-theoretic probability theory, a probability
> monad, a coupling / Kantorovich setup, or a randomness-extractor
> argument.

`NotProved-*` aliases at the bottom of `EchoProbabilisticSupport.agda`:
- `NotProved-measure-preserving`
- `NotProved-probability-monad`
- `NotProved-Kantorovich-distance`
- `NotProved-coupling-aware`
- `NotProved-randomness-extraction`

**Julia consequence.** `support_collapses_at(S, o)`,
`samp_residue_loses_index(S, o)`, etc. all witness the TYPE-LEVEL
support-tracking content: a marginal forgets the index, the Echo
retains it. Nothing about distributions, integrals, expected
values, couplings, or randomness sources.

**Category errors to avoid.**
- "We tested `support_collapses_at`, so the marginal preserves
  the measure." (No — there is no measure in the formalism.)
- "The test witnesses Kantorovich-distance." (No — there is no
  metric.)
- "This handles randomness extraction." (No — there's no source
  of randomness in the model.)

---

## EchoDifferential — the perturbation / privacy gap

Upstream pins:

> It is NOT differential privacy, NOT a Lipschitz / sensitivity-
> bound argument, NOT a noise-calibration result, NOT a privacy-
> vs-utility tradeoff, NOT an adversary model.

`NotProved-*` aliases:
- `NotProved-epsilon-DP`
- `NotProved-Lipschitz-bound`
- `NotProved-noise-calibrated`
- `NotProved-privacy-vs-utility`
- `NotProved-adversary-model`

**Julia consequence.** `blur_collapses_perturbations_at(S, v)` and
its companions witness that a blur forgets which perturbation
produced the value. Nothing about ε-budgets, noise distributions,
sensitivity calculations, or adversary capabilities.

**Category errors to avoid.**
- "We tested `blur_collapses_perturbations_at`, so this query is
  ε-DP for some ε." (No — there is no ε in the formalism.)
- "The blur is Lipschitz." (No — there is no metric.)
- "Privacy is preserved." (No — privacy is a quantitative claim
  about adversary advantage; the test is qualitative.)

---

## EchoProvenance — the type-level / semiring gap

Upstream pins:

> The abstract setup deliberately does NOT bake in any semiring
> structure on `Tag` — the headline theorems use only the
> tag-distinguishability witness.

**Julia consequence.** A green `provenance_collapses_at` witnesses
that the projection forgets the tag at every payload. It does NOT
witness K-provenance semiring laws, why-provenance trees,
where-provenance annotation propagation, or any specific
provenance algebra.

**Category errors to avoid.**
- "We tested Provenance, so K-provenance is correct in our
  database." (No — K-provenance is a semiring; the test uses no
  semiring structure.)

---

## EchoLLEncoding — the existence / universality gap

Upstream pins:

> This is an EXISTENCE statement: there exists a shallow LL
> encoding under which `no-section-weaken` fails to lift. It is
> NOT a universal statement that every conceivable LL-style
> encoding loses the property.

**Julia consequence.** `gap_paired()` shows one specific encoding
(`X m := ⊤`) has an encoded section while the source does not. It
does NOT show every LL-style encoding fails — a richer encoding
that retains the witness could in principle preserve no-section.
(See `EchoLLEncoding.agda` companion-remark.)

---

## A useful mental check

Before citing a green Julia test in a write-up, document, or PR
description, ask:

1. **What Agda lemma does this exhibit?** (Name the module + the
   exported theorem.)
2. **What does the upstream module's matched-negative block say
   the lemma does NOT mean?** (Open the Agda file and read it.)
3. **Is my claim within the scope the lemma's body actually
   proves?** (Not within the scope a casual reader might think
   from the lemma's name alone.)

If steps 2 or 3 surface a mismatch, narrow the claim. The test is
correct; the over-promotion is the bug.

---

## Why this matters

The four Tier-3 modules deliberately reuse audience-side
vocabulary ("audit", "support", "sensitivity", "provenance"). The
vocabulary is load-bearing for reach — a database engineer knows
"provenance", a DP practitioner knows "sensitivity". The risk is
that vocabulary carries assumptions the formalism doesn't satisfy.
The matched-negative blocks exist to head off exactly this
mismatch. The Julia package preserves them in testset comments;
this page collects them for citation.
