#!/bin/sh
# Fail if any headline theorem depends on an axiom.
#
# `make check` already fails on an admitted proof, but that does not catch a
# proof closed via an axiom (functional extensionality, classical logic, an
# Axiom someone added). This asks Rocq directly.
#
# Every theorem a Catalog.v row names, plus the reusable infrastructure.
set -eu
cd "$(dirname "$0")/.."

THMS="
S2389_139.fitted_label_is_tight
S603_284.fitted_label_sound
S603_284.lower_bound_is_only_linear
S1421_53.fitted_label_sound
S1421_53.second_parameter_is_spurious
S450_204.fitted_label_unsound
S5_100.fitted_label_not_tight
S5_100.iters_exponential_in_bitlength
S5_100.run_finishes
S167_177.fitted_label_not_tight
MergeSort.cost_msort_top
MergeSort.msort_top_sorted
MergeSort.msort_top_perm
S2389_139_Deep.prog_cost
S2389_139_Deep.run_aa
S5_100_Deep.prog_sqrt
S5_100_Deep.run_4
"

TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
{
  echo 'From BigOBench Require Import All.'
  for t in $THMS; do echo "Print Assumptions $t."; done
} > "$TMP/axioms.v"

OUT=$(rocq compile -Q theories BigOBench -o "$TMP/axioms.vo" "$TMP/axioms.v" 2>&1)

EXPECTED=$(echo "$THMS" | grep -c .)
CLOSED=$(printf '%s' "$OUT" | grep -c 'Closed under the global context' || true)

if printf '%s' "$OUT" | grep -qE '^(Axioms|Assumptions):'; then
  echo "FAIL: a theorem depends on an axiom"
  printf '%s\n' "$OUT"
  exit 1
fi

if [ "$CLOSED" -ne "$EXPECTED" ]; then
  echo "FAIL: expected $EXPECTED axiom-free theorems, Rocq reported $CLOSED"
  printf '%s\n' "$OUT"
  exit 1
fi

echo "OK: $CLOSED/$EXPECTED headline theorems closed under the global context"
