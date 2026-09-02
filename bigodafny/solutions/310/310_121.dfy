// 797_A. k-Factorization  (problem 310, solution 310_121)
// time complexity: O(logn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = [int(x) for x in input().split()]
// 
// sols = []
// curr_div = 2
// while n != 1 and len(sols) < k-1:
//     if n % curr_div == 0:
//         sols.append(curr_div)
//         n //= curr_div
//     else:
//         curr_div += 1
// 
// if len(sols) == k-1 and n != 1:
//     sols += [n]
//     sols = [str(x) for x in sols]
//     res = " ".join(sols)
//     print(res)
// else:
//     print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
  requires a >= 1
  decreases *
{
  var n := a;
  var k := b;
  var sols: seq<int> := [];
  var curr_div := 2;
  while n != 1 && |sols| < k - 1
    invariant 1 <= n
    decreases *
  {
    if n % curr_div == 0 {
      sols := sols + [curr_div];
      n := n / curr_div;
    } else {
      curr_div := curr_div + 1;
    }
  }
  if |sols| == k - 1 && n != 1 {
    sols := sols + [n];
    output := JoinInts(sols, " ") + "\n";
  } else {
    output := "-1\n";
  }
}
