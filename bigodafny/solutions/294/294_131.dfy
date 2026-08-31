// p03687 AtCoder Grand Contest 016 - Shrinking  (problem 294, solution 294_131)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin
// s= (stdin.readline().rstrip())
// f = lambda a, b: abs(a-b-1)
// diff = lambda ls: map(f, ls[1:], ls)
// 
// ans = 100
// for i in set(s):
//     ans = min(ans,max([len(j) for j in s.split(i)]))
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
