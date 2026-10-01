// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : main agent, override of labelaudit-r3-17
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Override of labelaudit-r3-17's other: the Python's table is the
//     literal range(2009) and d[x] fails unless x < 2009, so the source
//     caps the exponent; the Dafny guards 0 <= x < |d| the same way, each
//     of the n transactions costs O(1), and the class is O(n).
//
//   how this label could be wrong, and what to check:
//     The label's m is the bit length of 2**x. Check the Python's `d = [0
//     for i in range(2009)]`: d[x] fails for x >= 2009, so the literal
//     caps x and the 2**x work is constant per transaction.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 36, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInt"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 18_D. Seller Bob  (problem 2942, solution 2942_42)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// d = [0 for i in range(2009)]
// ans = 0
// for i in range(n): 
//   s = input().split()
//   x = int(s[1])
//   if s[0] == 'win':
//     d[x] = ans+ 2**x
//   else:
//     ans = max(d[x], ans)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, transactions: seq<seq<string>>) returns (output: string)
{
  var d: seq<int> := seq(2009, _ => 0);
  var ans := 0;
  var i := 0;
  while i < n
    invariant 0 <= i
    invariant |d| == 2009
    decreases n - i
  {
    if i < |transactions| && |transactions[i]| >= 2 {
      var kind := transactions[i][0];
      var x := ParseInt(transactions[i][1]);
      if 0 <= x < |d| {
        if kind == "win" {
          var p := 1;
          var e := 0;
          while e < x
            invariant 0 <= e <= x
            decreases x - e
          {
            p := p * 2;
            e := e + 1;
          }
          d := d[x := ans + p];
        } else {
          ans := if d[x] > ans then d[x] else ans;
        }
      }
    }
    i := i + 1;
  }
  output := IntToString(ans);
}
