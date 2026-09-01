// 282_B. Painting Eggs  (problem 1673, solution 1673_122)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// eggs=int(input())
// diff=0
// c=['A' for i in range(eggs)]
// for i in range(eggs):
//     a=int(input().split()[0])
// 
//     if a+diff<501:
//         diff+=a
//     else:
//         c[i]='G'
//         
//         diff-=1000-a
// print(''.join(c))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<int>>) returns (output: string)
{
  var diff := 0;
  var pieces: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var a := pairs[i][0];
    if a + diff < 501 {
      diff := diff + a;
      pieces := pieces + ["A"];
    } else {
      diff := diff - (1000 - a);
      pieces := pieces + ["G"];
    }
    i := i + 1;
  }
  output := Join(pieces, "");
}
