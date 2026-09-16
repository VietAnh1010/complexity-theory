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
//     sums := sums[i := prevSum2] and the other sums[i := ...] updates are
//     seq updates over the length-n sums sequence, and the `if sums[i]==0`
//     branch that triggers one of them runs on essentially every iteration
//     where no sell match set it, giving O(n) per write times O(n)
//     iterations, whereas Python's sum[i]=sum[i-1] is an O(1) in-place
//     list write making the Python genuinely O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes sums[i]:=... is O(1) as Python's sum[i]=... list
//     write is. Open the bottom of the loop body and confirm the `if
//     sums[i] == 0 { sums := sums[i := prevSum2]; }` branch fires on most
//     iterations (e.g. every 'win' day, since sums is only set by a
//     matching sell); if so this seq update on the length-n sums sequence
//     runs ~n times at O(n) each, giving O(n**2), while Python's sum list
//     mutation is O(1) in place.
//
//   structural facts (deterministic, from labelaudit.py):
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
