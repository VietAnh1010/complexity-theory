// 447_B. DZY Loves Strings  (problem 700, solution 700_99)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = input()
// k = int(input())
// w = [int(x) for x in input().split()]
// total = 0
// for i in range(len(t)):
//     total = total + w[ord(t[i])-97]*(i+1)
// for i in range(k):
//     total = total + max(w)*(len(t)+i+1)
// print(total)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
