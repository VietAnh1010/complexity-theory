// 1038_D. Slime  (problem 241, solution 241_47)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// if n==1:
//     print(a[0])
// elif all(ele>0 for ele in a):
//     s=sum(a)-2*min(a)
//     print(s)
// elif all(ele<0 for ele in a):
//     s=abs(sum(a))-2*abs(max(a))
//     print(s)
// else:
//     ans=0
//     for ele in a:
//         ans+=abs(ele)
//     print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1 && n == |a_list|
  ensures steps <= 10 * n + 10
{
  steps := 1;
  if n == 1 {
    output := IntToString(a_list[0]);
    steps := steps + 1;
  } else {
    var allPos := true;
    var allNeg := true;
    var k := 0;
    while k < n
      invariant 0 <= k <= n
      invariant steps <= 4 * k + 1
      decreases n - k
    {
      if a_list[k] <= 0 { allPos := false; }
      if a_list[k] >= 0 { allNeg := false; }
      k := k + 1;
      steps := steps + 4;
    }
    var ans: int;
    if allPos {
      ans := SumRange(a_list, 0, n) - 2 * MinSeq(a_list);
      steps := steps + n + n + 2;
    } else if allNeg {
      var total := SumRange(a_list, 0, n);
      var mx := MaxSeq(a_list);
      ans := AbsInt(total) - 2 * AbsInt(mx);
      steps := steps + n + n + 4;
    } else {
      var total := 0;
      var j := 0;
      while j < n
        invariant 0 <= j <= n
        invariant steps <= 4 * n + 1 + 3 * j + 2
        decreases n - j
      {
        total := total + AbsInt(a_list[j]);
        j := j + 1;
        steps := steps + 3;
      }
      ans := total;
    }
    output := IntToString(ans);
    steps := steps + 1;
  }
}

function SumRange(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0 else s[lo] + SumRange(s, lo + 1, hi)
}

function AbsInt(x: int): int
{
  if x < 0 then -x else x
}
