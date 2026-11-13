// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny makes one pass over s and one `MaxSeq` over the 26
//     weights, then adds a closed-form term in n, so the cost is O(|s|);
//     the Python's `max(w)` is likewise over a fixed 26 entries.
//
//   how this label could be wrong, and what to check:
//     The label's m can only be the weight list, but `w` always holds
//     exactly 26 values (one per letter; the Dafny requires `|a_list| ==
//     26`), and k enters only a closed-form product. Check the input
//     format: if w is fixed at 26, the only size is |s| and the class is
//     O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 19, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MaxSeq"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 447_B. DZY Loves Strings  (problem 700, solution 700_233)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// k=int(input())
// w=list(map(int,input().split()))
// score=0
// for i in range(len(s)):
//     score+=(w[ord(s[i])-97]*(i+1))
// 
// score=score+(max(w)*(k*len(s)+(k*(k+1)//2)))
// print(int(score))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == 26
  requires forall k :: 0 <= k < |s| ==> 'a' <= s[k] <= 'z'
{
  var total := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    var idx := (s[i] as int) - 97;
    total := total + a_list[idx] * (i + 1);
    i := i + 1;
  }
  var mx := MaxSeq(a_list);
  total := total + mx * (n * |s| + (n * (n + 1)) / 2);
  output := IntToString(total);
}
