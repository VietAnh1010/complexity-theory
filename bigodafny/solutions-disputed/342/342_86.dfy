// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Dafny's third loop runs `ISqrt(v)` and a divisor loop to sqrt(v)
//     for each of the n elements, O(n sqrt(max a_i)); the Python iterates
//     `set(a)`, so its divisor work is O(n + d sqrt(max a_i)) for d
//     distinct values.
//
//   how this label could be wrong, and what to check:
//     Two faults. Both programs run a divisor loop to sqrt(a_i), a value
//     term the O(n) label omits. The Python runs it once per DISTINCT
//     value (`for i in set(a)`); the Dafny runs it for every element of
//     `a_list`. Check the Dafny's third loop: it iterates `idx` over all n
//     elements with no deduplication.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 42, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1113_B. Sasha and Magnetic Machines  (problem 342, solution 342_86)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// input()
// a = list(map(int , input().split()))
// m = min(a)
// print(sum(a)-max(i+m-i//j-m*j for i in set(a)
// for j in range(1 , int(i**.5) + 1)if i%j==0))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| >= 1
{
  var total := 0;
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    total := total + a_list[idx];
    idx := idx + 1;
  }
  var m := a_list[0];
  idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    if a_list[idx] < m { m := a_list[idx]; }
    idx := idx + 1;
  }
  var diff := 0;
  idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    var v := a_list[idx];
    var r := ISqrt(v);
    var j := 1;
    while j <= r
      decreases r + 1 - j
    {
      if v % j == 0 {
        var term := v + m - v / j - m * j;
        if term > diff { diff := term; }
      }
      j := j + 1;
    }
    idx := idx + 1;
  }
  output := IntToString(total - diff);
}
