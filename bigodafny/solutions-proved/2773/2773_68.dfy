// 799_A. Carrot Cakes  (problem 2773, solution 2773_68)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,t,k,d = list(map(int,input().split()))
// fi = ((n+k-1)//k) * t
// t1 = 0
// t2 = d
// while n > 0:
//     n -= k
//     t1 += t
//     if n <= 0:
//         break
//     if t1 > d:
//         n-=k
//         t2+=t
//         if n <= 0:
//             break
// if t1 < fi or (t2 < fi and t2 != d):
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// k >= 1: the source's own `fi` computation treats k <= 0 as a degenerate
// case (fi := 0), and every test constraint for this problem has k >= 1.
// Without it, `n -= k` never shrinks n and the loop cannot be bounded at all.
method Solve(a: int, b: int, c: int, d: int) returns (output: string, ghost steps: nat)
  requires c >= 1
  ensures steps <= 6 * (if a > 0 then a else 0) + 10
{
  steps := 1;
  var n := a; var t := b; var k := c;
  var fi := if k > 0 then ((n + k - 1) / k) * t else 0;
  steps := steps + 2;
  var t1 := 0;
  var t2 := d;
  var stop := false;
  ghost var n0 := if n > 0 then n else 0;
  ghost var base1 := steps;
  while n > 0 && !stop
    invariant n <= n0
    invariant steps <= base1 + 6 * (n0 - (if n > 0 then n else 0)) + 6
    decreases (if n > 0 then n else 0)
  {
    n := n - k;
    t1 := t1 + t;
    steps := steps + 2;
    if n <= 0 {
      stop := true;
    } else if t1 > d {
      n := n - k;
      t2 := t2 + t;
      steps := steps + 2;
      if n <= 0 { stop := true; }
    }
    steps := steps + 2;
  }
  output := if t1 < fi || (t2 < fi && t2 != d) then "YES" else "NO";
  steps := steps + 1;
}
