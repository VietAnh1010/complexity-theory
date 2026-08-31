// 276_A. Lunch Rush  (problem 2012, solution 2012_342)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int, input().split())
// s = set()
// for i in range(n):
//     a,b=map(int, input().split())
//     if b > k:
//         s.add(a-(b-k))
//     else:
//         s.add(a)        
// print(max(s))        
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, pairs: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
