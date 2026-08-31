// 1131_B. Draw!  (problem 525, solution 525_234)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// count=1
// a,b=0,0
// for i in range(n):
//     c,d=map(int,input().split(' '))
//     if min(c,d)>=max(a,b):
//         if a!=b:
//             count+=min(c,d)-max(a,b)+1
//         else:
//             count+=min(c,d)-max(a,b)
//     a,b=c,d
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, points: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
