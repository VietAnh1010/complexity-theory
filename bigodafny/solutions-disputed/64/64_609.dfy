// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Python shifts the window with `a[1:] = a[:-1]`, O(k) per new id,
//     over n ids, so it is O(n*k); the Dafny's `a := [id] + a[..k - 1]` is
//     a concat charged k and matches it, with k a separate input value.
//
//   how this label could be wrong, and what to check:
//     The label squares one size, but the per-id shift `a[1:] = a[:-1]`
//     costs k, the window size, which is an input value separate from n.
//     Check that k is read from input and that the shift in the Python
//     copies k-1 slots; then the class is O(n*k), not O(n**2).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 28, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "JoinInts"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": true, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": true}
// --------------------------------------------------------------------

// 1234_B1. Social Network (easy version)  (problem 64, solution 64_609)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// a = [0] * k
// l = 0
// curr = set()
// 
// ids = map(int, input().split())
// 
// for id in ids:
//     if id not in curr:
//         curr.add(id)
// 
//         if a[-1] != 0:
//             curr.remove(a[-1])
// 
//         a[1:] = a[:-1]
//         a[0] = id
//         l = min(l + 1, k)
// 
// print(l)
// print(' '.join(map(str, a[:l])))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, ratings: seq<int>) returns (output: string)
  requires k >= 1
{
  var a: seq<int> := seq(k, i => 0);
  var l := 0;
  var curr: set<int> := {};
  var idx := 0;
  while idx < |ratings|
    invariant 0 <= idx <= |ratings|
    invariant |a| == k
    invariant 0 <= l <= k
    decreases |ratings| - idx
  {
    var id := ratings[idx];
    if id !in curr {
      curr := curr + {id};
      if a[k - 1] != 0 {
        curr := curr - {a[k - 1]};
      }
      a := [id] + a[..k - 1];
      l := if l + 1 < k then l + 1 else k;
    }
    idx := idx + 1;
  }
  output := IntToString(l) + "\n" + JoinInts(a[..l], " ");
}
