// 758_B. Blown Garland  (problem 2072, solution 2072_257)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// d={}
// n=len(s)
// for i in range(n):
//     if(s[i]!='!'):
//         d[i%4]=s[i]
// l={'R':0,'B':0,'Y':0,'G':0}
// for i in range(n):
//     if(s[i]=='!'):
//         l[d[i%4]]+=1
// print(*list(l.values()))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
