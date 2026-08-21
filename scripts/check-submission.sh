#!/usr/bin/env bash
set -euo pipefail

repository_root=$(cd "$(dirname "$0")/.." && pwd)
cd "$repository_root"

ruby scripts/validate-formalization.rb

unexpected=$(rg -n --glob '*.lean' \
  '(^|[^[:alnum:]_])(sorry|admit)\b|^[[:space:]]*axiom\b' \
  --glob '!Challenge.lean' . || true)
if [ -n "$unexpected" ]; then
  echo "error: proof development contains an admitted obligation or axiom:" >&2
  echo "$unexpected" >&2
  exit 1
fi

challenge_sorries=$(rg -o '\bsorry\b' Challenge.lean | wc -l | tr -d ' ')
if [ "$challenge_sorries" != "1" ]; then
  echo "error: Challenge.lean must contain exactly one deliberate sorry" >&2
  exit 1
fi

lake build FirstPassageLinearTransport Solution Audit
git diff --check

echo "submission preflight passed"
