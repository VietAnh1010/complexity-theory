// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-22
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     l1 := l1[i := 2*primes[i+1]] is a seq update on the length-n l1
//     sequence executed inside the while loop that runs about n-1 times,
//     costing O(n) per write and O(n**2) overall, whereas Python's
//     l1[i]=2*l[i+1] mutates a real list in place at O(1) per write and is
//     O(n) as labelled.
//
//   how this label could be wrong, and what to check:
//     The label assumes l1[i]:=... is O(1) as Python's in-place list
//     assignment is. Open the while loop and confirm it does `l1 := l1[i
//     := 2*primes[i+1]]`, a full seq copy of length n on every one of the
//     ~n iterations; if so the loop alone is O(n**2), while Python's
//     l1[i]=... and l1[-1]*=... are O(1) in-place writes making the Python
//     genuinely O(n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 29, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 0,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 66_D. Petya and His Friends  (problem 2926, solution 2926_50)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=[2	,3	,5	,7	,11	,13	,17	,19	,23	,29	,31	,37	,41	,43	,47	,53	,59	,61	,67	,71
// ,73	,79	,83	,89	,97	,101	,103	,107	,109	,113	,127	,131	,137	,139	,149	,151	,157	,163	,167	,173
// ,179	,181	,191	,193	,197	,199	,211	,223	,227	,229	,233	,239	,241]
// n=int(input())
// l1=[1 for i in range(n)]
// if n==2 :
//     print("-1")
//     exit()
// for i in range(n-1) :
//     l1[i]=2*l[i+1]
//     l1[-1]*=l[i+1]
// for x in l1 :
//     print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var primes := [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,
                 73,79,83,89,97,101,103,107,109,113,127,131,137,139,149,151,157,163,167,173,
                 179,181,191,193,197,199,211,223,227,229,233,239,241];
  if n == 2 {
    output := "-1\n";
  } else if n <= 0 {
    output := "";
  } else {
    var l1 := seq(n, _ => 1);
    var last := 1;
    var i := 0;
    while i < n - 1 && i + 1 < |primes|
      invariant 0 <= i
      invariant |l1| == n
      decreases n - 1 - i
    {
      l1 := l1[i := 2 * primes[i+1]];
      last := last * primes[i+1];
      i := i + 1;
    }
    l1 := l1[n - 1 := last];
    var lines := seq(n, k requires 0 <= k < n => IntToString(l1[k]));
    output := Join(lines, "\n") + "\n";
  }
}
