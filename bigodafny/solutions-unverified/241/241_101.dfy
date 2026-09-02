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

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1 && n == |a_list|
{
  if n == 1 {
    output := IntToString(a_list[0]);
  } else {
    var s := SortInts(a_list);
    var i := 0;
    while i < n && s[i] <= 0
      invariant 0 <= i <= n
      decreases n - i
    {
      i := i + 1;
    }
    var ans: int;
    if i == 0 {
      ans := SumRange(s, 0, n) - 2 * s[0];
    } else if i == n {
      ans := 2 * s[n - 1] - SumRange(s, 0, n);
    } else {
      ans := SumRange(s, i, n) - SumRange(s, 0, i);
    }
    output := IntToString(ans);
  }
}

function SumRange(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0 else s[lo] + SumRange(s, lo + 1, hi)
}
