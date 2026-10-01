// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-17
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The win branch runs `while e < x` to compute 2**x, so each of the n
//     transactions costs O(x) in an element VALUE, giving O(n * max x),
//     not a product of two input sizes; the Python pays the same through
//     bignum 2**x and ans+2**x, and the 2000 cap is a statement bound, not
//     a literal in the source.
//
//   how this label could be wrong, and what to check:
//     The label assumes m is a second input dimension, but transactions
//     rows are fixed two-element (kind, x) pairs, so no width m is
//     scanned. Check whether m was meant to be the exponent value x
//     (statement: 0 <= x <= 2000); if so the label is a value-term in
//     disguise and may be acceptable naming, otherwise it is wrong. Find
//     the inner `while e < x` loop in the win branch and compare with
//     `d[x] = ans + 2**x` in the Python.
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
