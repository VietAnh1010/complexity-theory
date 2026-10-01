// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-17
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     In the sell branch the Dafny runs `while e < m` (pw := pw * 2) for
//     every matched sell, so total cost is O(n * max m) with m an exponent
//     VALUE; CPython's 2**m and the bignum additions on it pay a matching
//     O(m) term, so the Python is not plain O(n) either.
//
//   how this label could be wrong, and what to check:
//     The label counts only the n transactions, but each sell of a known
//     stick loops `while e < m` to build 2**m, a cost in the element value
//     m. Open the sell branch and find that loop; then check the Python's
//     `2**m + sum[...]` which pays bignum cost proportional to m. If the
//     intended reading is that m is bounded by 2000 and treated as
//     constant, the label would stand, but the rules say a statement cap
//     does not make it constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 59, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInt"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 18_D. Seller Bob  (problem 2942, solution 2942_55)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=int(input())
// a={}
// sum=[]
// ls=-1
// for i in range(s):
//   sum.append(0)
// for i in range(s):
//   n, z = map(str, input().split())
//   m=int(z)
//   if(n=="win"):
//       a[m]=(1,i)
//   if (n=="sell"):
//     p = a.get(m, -1)
//     if(p!=-1):
//       if(sum[i-1]<2**m+sum[a[m][1]]):
//         sum[i]=2**m+sum[a[m][1]]
//         ls=i
//       else:
//         if(a[m][1]>ls):
//           sum[i]=2**m+sum[i-1]
//           ls=i
//   if(sum[i]==0):
//     sum[i]=sum[i-1]
// print(sum[s-1])
// 
// # Sun Mar 24 2019 13:38:31 GMT+0300 (MSK)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, transactions: seq<seq<string>>) returns (output: string)
{
  var s := n;
  var aIdx: seq<int> := seq(2009, _ => -1);
  var sums: seq<int> := seq(if s > 0 then s else 0, _ => 0);
  var ls := -1;
  var i := 0;
  while i < s
    invariant 0 <= i
    invariant |sums| == (if s > 0 then s else 0)
    invariant |aIdx| == 2009
    decreases s - i
  {
    if i < |transactions| && |transactions[i]| >= 2 {
      var kind := transactions[i][0];
      var m := ParseInt(transactions[i][1]);
      if kind == "win" {
        if 0 <= m < |aIdx| {
          aIdx := aIdx[m := i];
        }
      } else if kind == "sell" {
        if 0 <= m < |aIdx| && aIdx[m] != -1 {
          var winIdx := aIdx[m];
          var pw := 1;
          var e := 0;
          while e < m
            invariant 0 <= e <= m
            decreases m - e
          {
            pw := pw * 2;
            e := e + 1;
          }
          var prev := if i == 0 then 0 else sums[i - 1];
          var base := if 0 <= winIdx < |sums| then sums[winIdx] else 0;
          if prev < pw + base {
            sums := sums[i := pw + base];
            ls := i;
          } else if winIdx > ls {
            var prevSum := if i == 0 then 0 else sums[i - 1];
            sums := sums[i := pw + prevSum];
            ls := i;
          }
        }
      }
    }
    if sums[i] == 0 {
      var prevSum2 := if i == 0 then 0 else sums[i - 1];
      sums := sums[i := prevSum2];
    }
    i := i + 1;
  }
  if s > 0 {
    output := IntToString(sums[s - 1]);
  } else {
    output := IntToString(0);
  }
}
