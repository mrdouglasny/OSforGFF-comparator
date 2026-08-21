#!/usr/bin/env bash
# Source-level gate on the registry pair, complementing the Comparator run:
#   - no `axiom` declarations and no kernel escape hatches (`native_decide`, `unsafe`,
#     `@[implemented_by]`, `@[extern]`) in either file;
#   - Challenge.lean carries EXACTLY ONE `sorry` — the challenge hole;
#   - Solution.lean carries none.
#
# Comments are stripped before scanning, so prose that merely names `axiom` or `sorry`
# (as the module docstrings do) is not a false positive.
#
#   exit 0  → clean
#   exit 2  → violation; intended to BLOCK as a CI step.
#
# Usage:  scripts/check-pair.sh [REPO_ROOT]
set -uo pipefail

REPO="${1:-$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)}"
cd "$REPO" 2>/dev/null || { echo "check-pair: repo not found: $REPO" >&2; exit 2; }
[ -f Challenge.lean ] && [ -f Solution.lean ] || {
  echo "check-pair: Challenge.lean / Solution.lean not found in $REPO" >&2; exit 2; }

# Emit `path:lineno:code` for every line, with Lean comments removed: `--` to end of line,
# and nestable `/- … -/` blocks (which subsume `/-- … -/` docstrings).
strip_comments() {
  awk '
    FNR == 1 { depth = 0 }
    {
      line = $0; out = ""; i = 1; n = length(line)
      while (i <= n) {
        two = substr(line, i, 2)
        if (depth > 0) {
          if (two == "-/") { depth--; i += 2; continue }
          if (two == "/-") { depth++; i += 2; continue }
          i++; continue
        }
        if (two == "/-") { depth++; i += 2; continue }
        if (two == "--") { break }
        out = out substr(line, i, 1); i++
      }
      print FILENAME ":" FNR ":" out
    }
  ' "$@"
}

CODE="$(strip_comments Challenge.lean Solution.lean)"

fail=0
report() { # report <label> <findings>
  local label="$1" findings="$2"
  [ -z "$findings" ] && return 0
  echo "✗ BLOCK: $label" >&2
  printf '%s\n' "$findings" | sed 's/^/    /' >&2
  fail=1
}

axioms=$(printf '%s\n' "$CODE" \
  | grep -E '^[^:]+:[0-9]+:[[:space:]]*(private[[:space:]]+|protected[[:space:]]+)?axiom[[:space:]]' || true)
hatches=$(printf '%s\n' "$CODE" \
  | grep -E 'native_decide|(^|[^[:alnum:]_])unsafe([^[:alnum:]_]|$)|@\[implemented_by|@\[extern' || true)
nch=$(printf '%s\n' "$CODE" \
  | grep -cE '^Challenge\.lean:[0-9]+:.*(^|[^[:alnum:]_])(sorry|sorryAx|admit)([^[:alnum:]_]|$)' || true)
nsol=$(printf '%s\n' "$CODE" \
  | grep -cE '^Solution\.lean:[0-9]+:.*(^|[^[:alnum:]_])(sorry|sorryAx|admit)([^[:alnum:]_]|$)' || true)

report "axiom declaration(s) in the registry pair:" "$axioms"
report "kernel escape hatch in the registry pair:" "$hatches"
if [ "$nch" != "1" ]; then
  echo "✗ BLOCK: Challenge.lean sorry count = $nch (expected exactly 1: the challenge hole)" >&2
  fail=1
fi
if [ "$nsol" != "0" ]; then
  echo "✗ BLOCK: Solution.lean contains sorry/admit (it must be fully proved)" >&2
  fail=1
fi

if [ "$fail" -ne 0 ]; then
  echo "✗ pair gate BLOCK — resolve before continuing." >&2
  exit 2
fi
echo "✓ pair gate: clean — no axiom/escape-hatch; Challenge has exactly the challenge-hole sorry, Solution none"
