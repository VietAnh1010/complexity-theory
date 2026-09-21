// 797_A. k-Factorization  (problem 310, solution 310_51)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k=map(int, input().split())
// h=n
// t=""
// f=0
// i=2
// while k!=f+1 and i<=n/2:
//     if h%i==0:
//         f+=1
//         t+="{} ".format(i)
//         h=int(h/i)
//     else:
//         i+=1
// if k>f+1 or h==1:
//     print(-1)
// else:
//     print(t+"{}".format(h))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  requires a >= 1
  ensures steps <= 30 * a + 20
{
  steps := 1;
  var n := a;
  var k := b;
  var h := n;
  var parts: seq<string> := [];
  var f := 0;
  var i := 2;
  ghost var initPot := (n - 2) + h;
  while k != f + 1 && 2 * i <= n
    invariant h >= 1
    invariant n - i + h >= 0
    invariant |parts| <= initPot - (n - i + h)
    invariant steps <= 1 + 8 * (initPot - (n - i + h))
    decreases n - i, h
  {
    if h % i == 0 {
      f := f + 1;
      parts := parts + [IntToString(i)];
      h := h / i;
      steps := steps + 6;
    } else {
      i := i + 1;
      steps := steps + 2;
    }
  }
  if k > f + 1 || h == 1 {
    output := "-1\n";
    steps := steps + 1;
  } else {
    output := Join(parts, " ") + (if |parts| > 0 then " " else "") + IntToString(h) + "\n";
    steps := steps + 3 * |parts| + 3;
  }
}
