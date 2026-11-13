// 214_A. System of Equations  (problem 482, solution 482_543)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// c=0
// for i in range(0,n+1):
//     for j in range(0,m+1):
//         if(i**2+j==n and j**2+i==m):
//             c+=1
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function Cnt(x: int): nat { if x >= 0 then x + 1 else 0 }

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= Cnt(a) * (12 * Cnt(b) + 2) + |output| + 3
{
  steps := 1;
  var n := a;
  var m := b;
  var c := 0;
  var i := 0;
  ghost var K := 12 * Cnt(b) + 2;
  while i <= n
    invariant 0 <= i <= Cnt(a)
    invariant n == a && m == b
    invariant steps == 1 + i * K
    decreases n - i
  {
    var j := 0;
    ghost var s0 := steps;
    while j <= m
      invariant 0 <= j <= Cnt(b)
      invariant steps == s0 + 12 * j
      decreases m - j
    {
      if i * i + j == n && j * j + i == m {
        c := c + 1;
      }
      j := j + 1;
      steps := steps + 12;
    }
    assert j == Cnt(b);
    i := i + 1;
    steps := steps + 2;
    CostMulDistrib(i - 1, 1, i, K);
    assert 1 * K == K;
  }
  output := IntToString(c);
  IntToStringDigits(c);
  steps := steps + Digits(c);
}
