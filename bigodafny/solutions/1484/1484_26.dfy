// 172_A. Phone Code  (problem 1484, solution 1484_26)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=[];i=0
// for _ in range(int(input())):l.append(input())
// a=max(l);b=min(l)
// while a[i]==b[i]:i+=1
// print(i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
