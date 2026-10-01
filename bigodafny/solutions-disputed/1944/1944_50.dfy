// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : translation
//   confidence     : medium
//   auditor        : labelaudit-r3-10
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     CeilSqrt reimplements the sqrt library call with a hi := hi * 2 loop
//     and a binary search, so each of the n tests costs O(log s_i), giving
//     O(n log max s); Python's math.sqrt is O(1) per test, so the label
//     fits the Python only. The statement cap s<=5000 is not a source
//     literal.
//
//   how this label could be wrong, and what to check:
//     The label counts test cases only, but the Dafny's CeilSqrt does a
//     doubling loop plus a binary search per test, costing O(log s) in the
//     test's value. Check CeilSqrt in the Dafny against
//     math.ceil(math.sqrt(...)) in the Python, which is a single library
//     call per test; if the Python call is O(1) the translation introduced
//     the value term.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 37, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 3, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1550_A. Find The Array  (problem 1944, solution 1944_50)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// t=int(input())
// for i in range(t):
//     print(math.ceil(math.sqrt(int(input()))))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Smallest r >= 0 with r*r >= x, i.e. ceil(sqrt(x)) over the integers.
// Binary search, so a large x costs log(x) and not sqrt(x).
method CeilSqrt(x: int) returns (r: int)
  requires x >= 0
  ensures r >= 0
{
  if x <= 1 { return x; }
  var hi := 1;
  while hi * hi < x
    invariant hi >= 1
    decreases x - hi * hi
  {
    hi := hi * 2;
  }
  var lo := 0;
  while lo < hi
    invariant 0 <= lo <= hi
    decreases hi - lo
  {
    var mid := (lo + hi) / 2;
    if mid * mid >= x { hi := mid; } else { lo := mid + 1; }
  }
  return lo;
}

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |numbers|
    decreases |numbers| - i
  {
    var r := CeilSqrt(if numbers[i] >= 0 then numbers[i] else 0);
    parts := parts + [IntToString(r)];
    i := i + 1;
  }
  output := Join(parts, "\n") + "\n";
}
