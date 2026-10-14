// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : io-rule-2026-10-14
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Two passes over pairs with O(1) map work each; the only width walked
//     is ParseInt reading each input token once, which is input length and
//     excluded, and no row is ever scanned beyond its first two tokens.
//     The sibling 378_91 has the same loops and a proof of O(n).
//
//   how this label could be wrong, and what to check:
//     The label names m, but nothing walks a pair beyond reading its two
//     tokens. Check both loops in Solve: each does O(1) map work per pair
//     after one ParseInt. If you count token width as work rather than
//     input, the label stands.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 48, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "ParseInt",
//     "ParseIntFrom"], "loop_depth": 1, "loops": 2, "recursive_helpers":
//     2, "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": true, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 432_B. Football Kit  (problem 378, solution 378_20)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// x=[]
// for i in range(n):
//     x.append(list(map(int,input().split())))
//  
// h={}
// a={}
// for i in range(n):
//     if(h.get(str(x[i][0]))):
//         h[str(x[i][0])]+=1
//     else:
//         h[str(x[i][0])]=1
//     
// for i in range(n):
//     home=n-1
//     if(h.get(str(x[i][1]))):
//         if(h[str(x[i][1])]>0):
//             away= n-1-h[str(x[i][1])]
//             home+=h[str(x[i][1])]
//     else:
//         away=n-1
//     print(home,away)   
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string)
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
{
  var h: map<int, int> := map[];
  var idx := 0;
  while idx < |pairs|
    decreases |pairs| - idx
  {
    var home0 := ParseInt(pairs[idx][0]);
    if home0 in h {
      h := h[home0 := h[home0] + 1];
    } else {
      h := h[home0 := 1];
    }
    idx := idx + 1;
  }
  var lines: seq<string> := [];
  idx := 0;
  while idx < |pairs|
    decreases |pairs| - idx
  {
    var away0 := ParseInt(pairs[idx][1]);
    var home := n - 1;
    var away := n - 1;
    if away0 in h {
      var cnt := h[away0];
      away := n - 1 - cnt;
      home := home + cnt;
    }
    lines := lines + [IntToString(home) + " " + IntToString(away)];
    idx := idx + 1;
  }
  output := Join(lines, "\n");
}
