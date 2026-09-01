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
  var sa := 0;
  var sg := 0;
  var pieces: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var a := pairs[i][0];
    var g := pairs[i][1];
    if sa - sg + a <= 500 {
      pieces := pieces + ["A"];
      sa := sa + a;
    } else {
      pieces := pieces + ["G"];
      sg := sg + g;
    }
    i := i + 1;
  }
  output := Join(pieces, "");
}
