// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : unclear
//   confidence     : low
//   auditor        : labelaudit-r3-10
//
//   Which of the label or the translation is at fault was not determined
//   by the audit.
//
//   evidence:
//     The single loop runs over |s| with st + [x] amortised O(1) and a
//     slice pop O(1); m enters only through the constant-time arithmetic
//     req := n - m, so the cost is O(|s|), which is O(n) in the signature.
//
//   how this label could be wrong, and what to check:
//     The label names a second dimension m, but the Dafny's m is the
//     integer k used only in req := n - m, never scanned. Check that the
//     only loop is while i < |s| and that no other construct depends on m;
//     since the problem guarantees k <= n the label could still be the
//     same rank as O(n), so decide whether a value bounded by the first
//     variable is a naming difference.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 32, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 0, "seq_append_read_in_same_loop": true,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1023_C. Bracket Subsequence  (problem 1935, solution 1935_61)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// R = lambda:list(map(int,input().split()))
// n,t = R()
// s = input()
// 
// st = []
// req = n-t
// flag = 0
// for x in s:
//     if(x==")" and flag==0 and req>0):
//         req-=2
//         st.pop()
//         if(req==0):
//             flag = 1
//     else:
//         st.append(x)
// print("".join(st))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
  // |st| == i - 2*pops, and a pop only ever happens on a ')'. Fewer than half
  // of any prefix ending at a ')' are ')', so 2*pops <= i-1 and |st| >= 1.
  requires forall t :: 0 <= t < |s| && s[t] == ')' ==> 2 * Closes(s, t) < t
{
  var st: seq<char> := [];
  var req := n - m;
  var flag := 0;
  var i := 0;
  ghost var pops := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant 0 <= pops
    invariant |st| == i - 2 * pops
    invariant pops <= Closes(s, i)
    decreases |s| - i
  {
    var x := s[i];
    if x == ')' && flag == 0 && req > 0 {
      assert 2 * Closes(s, i) < i;
      assert |st| >= 1;
      req := req - 2;
      st := st[..|st|-1];
      pops := pops + 1;
      if req == 0 { flag := 1; }
    } else {
      st := st + [x];
    }
    i := i + 1;
  }
  output := st + "\n";
}
