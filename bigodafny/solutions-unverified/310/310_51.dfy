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

method Solve(a: int, b: int) returns (output: string)
  requires a >= 1
{
  var n := a;
  var k := b;
  var h := n;
  var parts: seq<string> := [];
  var f := 0;
  var i := 2;
  while k != f + 1 && 2 * i <= n
    invariant h >= 1
    decreases n - i, h
  {
    if h % i == 0 {
      f := f + 1;
      parts := parts + [IntToString(i)];
      h := h / i;
    } else {
      i := i + 1;
    }
  }
  if k > f + 1 || h == 1 {
    output := "-1\n";
  } else {
    output := Join(parts, " ") + (if |parts| > 0 then " " else "") + IntToString(h) + "\n";
  }
}
