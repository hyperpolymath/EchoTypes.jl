<!--
SPDX-License-Identifier: MPL-2.0
Copyright (c) Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->
# wiki/ — canonical source for the EchoTypes.jl wiki

This directory holds the canonical source of the EchoTypes.jl wiki
pages. The same content also lives at the GitHub wiki
([https://github.com/hyperpolymath/EchoTypes.jl/wiki](https://github.com/hyperpolymath/EchoTypes.jl/wiki))
when initialized; this in-repo copy is the **source of truth** so
edits land via PR review like any other file.

## Pages

- [Home.md](Home.md) — entry point + coverage map + carve-outs
- [Exercises.md](Exercises.md) — 10 hands-on REPL exercises with
  Agda links + extend-this prompts
- [Honest-Bound-Discipline.md](Honest-Bound-Discipline.md) —
  category-error catalogue for the Tier-3 audience surfaces
- [Adding-A-New-Shadow.md](Adding-A-New-Shadow.md) — PR submission
  guide for proposing new finite shadows

## Cross-repo bridge

The upstream-side mirror lives at
[echo-types/wiki/Julia-Companion-Exercises](https://github.com/hyperpolymath/echo-types/wiki/Julia-Companion-Exercises).
Both pages contain the same 10 exercises from their respective
repo's perspective.

## How to mirror to GitHub Wiki

If the GitHub wiki at
[hyperpolymath/EchoTypes.jl/wiki](https://github.com/hyperpolymath/EchoTypes.jl/wiki)
hasn't been initialized yet (a fresh wiki needs at least one page
created via the web UI before its git repo becomes pushable):

1. Visit the wiki tab and create any page (e.g., paste this
   README's content into a "Home" page and save). This bootstraps
   the wiki's git repo on GitHub.
2. Clone the wiki repo locally:
   ```
   git clone git@github.com:hyperpolymath/EchoTypes.jl.wiki.git
   ```
3. Copy these files in:
   ```
   cp wiki/*.md path/to/EchoTypes.jl.wiki/
   cd path/to/EchoTypes.jl.wiki
   git add . && git commit -m "sync from repo wiki/" && git push
   ```

Once mirrored, keep both sides in sync by editing here (in-repo)
and re-running the copy + push above.
