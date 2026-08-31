// 1244_A. Pens and Pencils  (problem 89, solution 89_909)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = input()
// n = int(n)
// for i in range(0,n):
//     l= input()
//     a,b,c,d,k = l.split()
//     a= int(a)
//     b= int(b)
//     c= int(c)
//     d= int(d)
//     k= int(k)
//     if (a%c!=0):
//         pens = int(a/c) + 1
//     else:
//         pens = int(a/c)
//     if (b%d!=0):
//         pins = int(b/d) + 1
//     else:
//         pins = int(b/d)
//     if ((pins+pens)>k):
//         print(-1)
//     else:
//         print(pens,pins)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
