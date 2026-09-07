// 1425_H. Huge Boxes of Animal Toys  (problem 1170, solution 1170_62)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// 
// for tc in range(t):
// 
//     a, b, c, d = map(int, input().split())
// 
//     k = ["Tidak"] * 4
// 
//     if not (a+b) % 2:
//         if (b+c):
//             k[2] = "Ya"
//         if (a+d):
//             k[3] = "Ya"
//     else:
//         if (b+c):
//             k[1] = "Ya"
//         if (a+d):
//             k[0] = "Ya"
// 
//     print(*k)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrices: seq<seq<int>>) returns (output: string)
  requires forall i :: 0 <= i < |matrices| ==> |matrices[i]| >= 4
{
  var parts: seq<string> := [];
  var idx := 0;
  while idx < |matrices|
    invariant 0 <= idx <= |matrices|
    decreases |matrices| - idx
  {
    var l := matrices[idx];
    var a := l[0];
    var b := l[1];
    var c := l[2];
    var d := l[3];
    var k0 := "Tidak";
    var k1 := "Tidak";
    var k2 := "Tidak";
    var k3 := "Tidak";
    if (a + b) % 2 == 0 {
      if b + c != 0 { k2 := "Ya"; }
      if a + d != 0 { k3 := "Ya"; }
    } else {
      if b + c != 0 { k1 := "Ya"; }
      if a + d != 0 { k0 := "Ya"; }
    }
    parts := parts + [k0 + " " + k1 + " " + k2 + " " + k3 + "\n"];
    idx := idx + 1;
  }
  output := Join(parts, "");
}
