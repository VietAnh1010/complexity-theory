// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny builds `distinct` with linear membership scans and
//     recounts the whole of `ratings` for each distinct value in
//     `CountOccurrences659b`, O(n**2); the Python's `dic.get(i, 0) + 1`
//     counts in one O(n) pass.
//
//   how this label could be wrong, and what to check:
//     The Python counts with a dict in one pass, O(n) as labelled. Check
//     the Dafny: it keeps `distinct` as a seq with linear `!in` tests and
//     calls `CountOccurrences659b` over all of `ratings` per distinct
//     value, both O(n**2) when all values differ.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 36, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 127_B. Canvas Frames  (problem 659, solution 659_55)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = input()
// a = a.split()
// dic = {}
// for i in a:
//     dic[i] = dic.get(i, 0) + 1
// c = 0
// for v in dic.values():
//     c += v//2
// print(c//2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, ratings: seq<int>) returns (output: string)
{
  var distinct: seq<int> := [];
  var i := 0;
  while i < |ratings|
    decreases |ratings| - i
  {
    if ratings[i] !in distinct {
      distinct := distinct + [ratings[i]];
    }
    i := i + 1;
  }
  var c := 0;
  i := 0;
  while i < |distinct|
    decreases |distinct| - i
  {
    var cnt := CountOccurrences659b(ratings, distinct[i]);
    c := c + cnt / 2;
    i := i + 1;
  }
  output := IntToString(c / 2);
}

method CountOccurrences659b(xs: seq<int>, v: int) returns (cnt: int)
{
  cnt := 0;
  var i := 0;
  while i < |xs|
    decreases |xs| - i
  {
    if xs[i] == v { cnt := cnt + 1; }
    i := i + 1;
  }
}
