// 486_C. Palindrome Transformation  (problem 1387, solution 1387_34)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,p = map(int,input().split())
// s = input()
// p = n-p if p > n//2 else p-1
// left,right,steps = n//2,-1,0
// for i in range(n//2):
//     x = abs(ord(s[i]) - ord(s[-i-1]))
//     steps += min(x,26-x)
//     if (x!=0) :
//         left = min(left,i)
//         right = max(right,i)
// if (steps) :
//     print (steps + right-left + min(abs(p-left),abs(right-p)))
// else:
//     print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function MinInt1387b(a: int, b: int): int { if a < b then a else b }

method Solve(n: int, k: int, s: string) returns (output: string, ghost steps: nat)
  requires n == |s|
  ensures steps <= 10 * n + 20
{
  steps := 1;
  var half := n / 2;
  var p := if k > half then n - k else k - 1;
  var left := half;
  var right := -1;
  var stepsv := 0;
  var i := 0;
  while i < half
    invariant 0 <= i <= half
    invariant steps <= 10 * i + 3
    decreases half - i
  {
    var x := AbsInt((s[i] as int) - (s[n-1-i] as int));
    stepsv := stepsv + MinInt1387b(x, 26 - x);
    steps := steps + 8;
    if x != 0 {
      if i < left { left := i; }
      if i > right { right := i; }
      steps := steps + 2;
    }
    i := i + 1;
  }
  if stepsv != 0 {
    output := IntToString(stepsv + right - left + MinInt1387b(AbsInt(p-left), AbsInt(right-p)));
    steps := steps + 6;
  } else {
    output := "0";
    steps := steps + 1;
  }
  assert half <= n;
}
