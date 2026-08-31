// p03072 AtCoder Beginner Contest 124 - Great Ocean View  (problem 1741, solution 1741_12)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// h = list(map(int,input().split()))
// c = 0
// for i in range(n):
//     if h[i]>=max(h[:i+1]):
//         c+=1
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, scores: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
