// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-fix
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Inside the loop over i < s, each 'sell' branch with m in a calls
//     Pow2_55(m), a recursive helper of depth O(log m) in the exponent
//     value, so the cost is O(n log max x) rather than O(n); the Python
//     pays the same value term in 2**m, so the translation is faithful and
//     the label omits it.
//
//   how this label could be wrong, and what to check:
//     The label counts only the n day lines, but each sell line with a
//     stored win calls Pow2_55(m), a squaring recursion of depth log m in
//     the exponent VALUE m (the x in 'sell x'), and the statement's cap 0
//     <= x <= 2000 does not make that constant under the value-term rule.
//     Open Pow2_55 and the Python's 2**m: if you hold that a
//     bounded-exponent power is a constant and the ParseInt on a
//     4-character token is a constant width, O(n) stands; otherwise the
//     class is O(n log max x).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 58, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInt"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": true, "uses_multiset": false, "uses_set": false}
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
  var a: map<int, int> := map[];
  var sums: seq<int> := seq(if s > 0 then s else 0, _ => 0);
  var ls := -1;
  var i := 0;
  while i < s
    invariant 0 <= i
    invariant |sums| == (if s > 0 then s else 0)
    decreases s - i
  {
    if i < |transactions| && |transactions[i]| >= 2 {
      var kind := transactions[i][0];
      var m := ParseInt(transactions[i][1]);
      if kind == "win" {
        a := a[m := i];
      } else if kind == "sell" {
        if m in a && m >= 0 {
          var winIdx := a[m];
          var pw := Pow2_55(m);
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

// 2**e by squaring: depth log e, as Python's ** is one operation
function Pow2_55(e: int): int
  requires e >= 0
  ensures Pow2_55(e) >= 1
  decreases e
{
  if e == 0 then 1
  else
    var h := Pow2_55(e / 2);
    if e % 2 == 0 then h * h else 2 * h * h
}
