// 999_C. Alphabetic Removals  (problem 2725, solution 2725_319)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=list(map(int,input().split()))
// s=list(input())
// x=sorted([j,i] for i,j in enumerate(s))
// #print(x)
// for i in range(k):
//     s[x[i][1]]=''
// print(''.join(s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
