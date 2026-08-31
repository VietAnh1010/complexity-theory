// 1113_B. Sasha and Magnetic Machines  (problem 342, solution 342_86)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// input()
// a = list(map(int , input().split()))
// m = min(a)
// print(sum(a)-max(i+m-i//j-m*j for i in set(a)
// for j in range(1 , int(i**.5) + 1)if i%j==0))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
