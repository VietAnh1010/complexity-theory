// 1038_D. Slime  (problem 241, solution 241_101)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int, input().split()))
// a.sort()
// if n==1:
//     print(a[0])
// else:
//     i=0
//     while i<n and a[i]<=0:
//         i+=1
//     if i==0:
//         print(sum(a)-2*a[0])
//     elif i==n:
//         print(2*a[-1]-sum(a))
//     else:
//         print(sum(a[i:])-sum(a[:i]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 1 && n == |a_list|
  ensures steps <= 2 * n * (CeilLog2(n) + 1) + 4 * n + 10
{
  if n == 1 {
    output := IntToString(a_list[0]);
    steps := 2;
  } else {
    SortCostTreeBound(n);
    steps := 1 + SortCost(n);
    var s := SortInts(a_list);
    var i := 0;
    while i < n && s[i] <= 0
      invariant 0 <= i <= n
      invariant steps <= 1 + SortCost(n) + 2 * i
      decreases n - i
    {
      i := i + 1;
      steps := steps + 2;
    }
    var ans: int;
    if i == 0 {
      ans := SumRange(s, 0, n) - 2 * s[0];
      steps := steps + n + 2;
    } else if i == n {
      ans := 2 * s[n - 1] - SumRange(s, 0, n);
      steps := steps + n + 2;
    } else {
      ans := SumRange(s, i, n) - SumRange(s, 0, i);
      steps := steps + (n - i) + i + 1;
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
