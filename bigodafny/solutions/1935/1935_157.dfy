// 1023_C. Bracket Subsequence  (problem 1935, solution 1935_157)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// ans=(n-k)//2
// s=input()
// s=s.replace("(","",ans)
// s=s.replace(")","",ans)
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
