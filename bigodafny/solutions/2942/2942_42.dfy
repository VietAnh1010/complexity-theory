// 18_D. Seller Bob  (problem 2942, solution 2942_42)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// d = [0 for i in range(2009)]
// ans = 0
// for i in range(n): 
//   s = input().split()
//   x = int(s[1])
//   if s[0] == 'win':
//     d[x] = ans+ 2**x
//   else:
//     ans = max(d[x], ans)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, transactions: seq<seq<string>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
