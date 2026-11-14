#!/bin/sh
# SPDX-License-Identifier: MPL-2.0
#
# check-agda-citations.sh: keep EchoTypes' Agda citations true.
#
# The Julia docstrings and comments cite the echo-types lemmas they mirror as
# backticked names, for example `echo-intro`. A backticked name that contains
# a hyphen cannot be a Julia identifier, so it is taken to be an Agda name.
# test/agda-citations.txt records every such name and the echo-types commit
# they were checked against.
#
# Usage:
#   scripts/check-agda-citations.sh extract
#       Print the cited names found in src/, one per line, sorted.
#   scripts/check-agda-citations.sh verify <echo-types checkout>
#       Check that the fixture matches src/, and that every name in it is
#       declared in an .agda file of the checkout. Exit 0 when both hold,
#       1 when either fails, 2 on a setup error.
#
# Scope: ASCII names only (letters, digits, hyphens). Names with Unicode or
# other symbols are not checked. The check is name-level: it proves the cited
# lemma exists, not that the Julia shadow agrees with it.
set -eu

ROOT=$(CDPATH= cd -- "$(dirname -- "$0")/.." && pwd)
FIXTURE="$ROOT/test/agda-citations.txt"

extract() {
  grep -ohE '`[A-Za-z][A-Za-z0-9]*(-[A-Za-z0-9]+)+`' "$ROOT"/src/*.jl \
    | tr -d '`' | LC_ALL=C sort -u
}

fixture_names() {
  grep -vE '^[[:space:]]*(#|$)' "$FIXTURE" | LC_ALL=C sort -u
}

case "${1:-}" in
  extract)
    extract
    ;;
  verify)
    AGDA_DIR="${2:-}"
    if [ -z "$AGDA_DIR" ] || [ ! -d "$AGDA_DIR" ]; then
      echo "check-agda-citations: give an echo-types checkout directory" >&2
      exit 2
    fi
    if [ ! -f "$FIXTURE" ]; then
      echo "check-agda-citations: missing $FIXTURE" >&2
      exit 2
    fi
    fail=0
    tmp_src=$(mktemp); tmp_fix=$(mktemp)
    trap 'rm -f "$tmp_src" "$tmp_fix"' EXIT
    extract >"$tmp_src"
    fixture_names >"$tmp_fix"
    if ! diff -u "$tmp_fix" "$tmp_src" >/dev/null; then
      echo "FAIL: test/agda-citations.txt does not match the names cited in src/:" >&2
      diff -u "$tmp_fix" "$tmp_src" | sed -n '3,$p' | grep -E '^[+-]' >&2 || true
      fail=1
    fi
    missing=0
    while IFS= read -r name; do
      if ! grep -rqE "^[[:space:]]*${name}[[:space:]]+:" --include='*.agda' "$AGDA_DIR"; then
        echo "MISSING in echo-types: $name" >&2
        missing=$((missing + 1))
      fi
    done <"$tmp_fix"
    total=$(wc -l <"$tmp_fix" | tr -d ' ')
    if [ "$missing" -ne 0 ]; then
      echo "FAIL: $missing of $total cited Agda names are not declared in $AGDA_DIR" >&2
      fail=1
    fi
    [ "$fail" -eq 0 ] && echo "PASS: $total cited Agda names match the fixture and are declared in echo-types"
    exit "$fail"
    ;;
  *)
    echo "usage: $0 extract | verify <echo-types checkout>" >&2
    exit 2
    ;;
esac
