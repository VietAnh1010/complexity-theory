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

// The `2**m` doubling loop only runs when 0 <= m < |aIdx| == 2009: that bound
// is a literal in the source (the aIdx array size), not a function of n, so
// it is a constant however large -- COMPLEXITY.md "value vs size". Every
// per-transaction cost is therefore O(1) and the total is O(n).
method Solve(n: int, transactions: seq<seq<string>>) returns (output: string, ghost steps: nat)
  ensures steps <= 4040 * (if n > 0 then n else 0) + 10
{
  steps := 1;
  var s := n;
  var aIdx: seq<int> := seq(2009, _ => -1);
  var sums: seq<int> := seq(if s > 0 then s else 0, _ => 0);
  var ls := -1;
  var i := 0;
  steps := steps + 2;
  ghost var base1 := steps;
  while i < s
    invariant 0 <= i
    invariant i <= (if s > 0 then s else 0)
    invariant |sums| == (if s > 0 then s else 0)
    invariant |aIdx| == 2009
    invariant steps <= base1 + 4040 * i
    decreases s - i
  {
    if i < |transactions| && |transactions[i]| >= 2 {
      var kind := transactions[i][0];
      var m := ParseInt(transactions[i][1]);
      steps := steps + 3;
      if kind == "win" {
        if 0 <= m < |aIdx| {
          aIdx := aIdx[m := i];
          steps := steps + 1;
        }
      } else if kind == "sell" {
        if 0 <= m < |aIdx| && aIdx[m] != -1 {
          var winIdx := aIdx[m];
          var pw := 1;
          var e := 0;
          steps := steps + 3;
          ghost var base2 := steps;
          while e < m
            invariant 0 <= e <= m
            invariant m < 2009
            invariant steps <= base2 + e
            decreases m - e
          {
            pw := pw * 2;
            e := e + 1;
            steps := steps + 1;
          }
          var prev := if i == 0 then 0 else sums[i - 1];
          var base := if 0 <= winIdx < |sums| then sums[winIdx] else 0;
          steps := steps + 2;
          if prev < pw + base {
            sums := sums[i := pw + base];
            ls := i;
            steps := steps + 2;
          } else if winIdx > ls {
            var prevSum := if i == 0 then 0 else sums[i - 1];
            sums := sums[i := pw + prevSum];
            ls := i;
            steps := steps + 3;
          }
        }
      }
    }
    if sums[i] == 0 {
      var prevSum2 := if i == 0 then 0 else sums[i - 1];
      sums := sums[i := prevSum2];
      steps := steps + 2;
    }
    i := i + 1;
    steps := steps + 1;
  }
  if s > 0 {
    output := IntToString(sums[s - 1]);
  } else {
    output := IntToString(0);
  }
  steps := steps + 2;
}
