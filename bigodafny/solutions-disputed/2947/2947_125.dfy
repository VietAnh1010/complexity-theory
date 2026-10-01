// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-r3d-08
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny replaces the Python dict with parallel keys/vals seqs and
//     rescans keys for each of the n likes, giving O(n * distinct) =
//     O(n**2). The Python's score dict makes each update O(1), so it is
//     O(n) as labelled; the dict-to-linear-search swap is an algorithm
//     replacement, not a container update.
//
//   how this label could be wrong, and what to check:
//     The label matches the Python's dict `score`, which is O(1) per vote.
//     Check the inner `while p < |keys|` loop in the Dafny that linearly
//     scans keys for every like; with many distinct ids it makes the whole
//     thing quadratic.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 40, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     true, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 637_A. Voting for Photos  (problem 2947, solution 2947_125)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(x) for x in input().split()]
// score = dict()
// sup, winner = -2**31, None
// for v in a:
//     score[v] = score[v] + 1 if v in score else 1
//     if score[v] > sup:
//         sup, winner = score[v], v
// print(winner)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var keys: seq<int> := [];
  var vals: seq<int> := [];
  var sup := -2147483648;
  var winner := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant |keys| == |vals|
    decreases |a_list| - i
  {
    var v := a_list[i];
    var idx := -1;
    var p := 0;
    while p < |keys|
      invariant 0 <= p <= |keys|
      invariant idx == -1 || (0 <= idx < p && keys[idx] == v)
      decreases |keys| - p
    {
      if keys[p] == v { idx := p; }
      p := p + 1;
    }
    if idx == -1 {
      keys := keys + [v];
      vals := vals + [1];
      idx := |keys| - 1;
    } else {
      vals := vals[idx := vals[idx] + 1];
    }
    if 0 <= idx < |vals| && vals[idx] > sup {
      sup := vals[idx];
      winner := v;
    }
    i := i + 1;
  }
  output := IntToString(winner);
}
