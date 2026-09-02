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

method Solve(a: int, b: int, c: int, d: int) returns (output: string)
  decreases *
{
  var n := a; var t := b; var k := c;
  var fi := if k > 0 then ((n + k - 1) / k) * t else 0;
  var t1 := 0;
  var t2 := d;
  var stop := false;
  while n > 0 && !stop
    decreases *
  {
    n := n - k;
    t1 := t1 + t;
    if n <= 0 {
      stop := true;
    } else if t1 > d {
      n := n - k;
      t2 := t2 + t;
      if n <= 0 { stop := true; }
    }
  }
  output := if t1 < fi || (t2 < fi && t2 != d) then "YES" else "NO";
}
