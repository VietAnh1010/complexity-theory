// 282_B. Painting Eggs  (problem 1673, solution 1673_129)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// sa,sg=0,0
// ans=''
// for _ in range(int(input())):
//     a,g=map(int,input().split())
//     if sa-sg+a<=500:
//         ans+='A'
//         sa+=a
//     else:
//         ans+='G'
//         sg+=g
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
