// 758_B. Blown Garland  (problem 2072, solution 2072_40)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// arr = input()
// n = len(arr)
// r, b, y, g = 0, 0, 0, 0
// 
// for i in range(4):
//     if i >= n:
//         break
//     ltrs = sorted(arr[i::4])
//     let = ltrs[len(ltrs) - 1]
//     a = ltrs.count('!')
//     if let == 'R':
//         r += a
//     elif let == 'B':
//         b += a
//     elif let == 'Y':
//         y += a
//     elif let == 'G':
//         g += a
// 
// print(r, b, y, g)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var n := |s|;
  var r := 0;
  var b := 0;
  var y := 0;
  var g := 0;
  var i := 0;
  while i < 4 && i < n
    decreases 4 - i
  {
    var ltrs: seq<char> := [];
    var j := i;
    while j < n
      decreases n - j
    {
      ltrs := ltrs + [s[j]];
      j := j + 4;
    }
    var sorted := Sort(ltrs, (x: char, z: char) => x < z);
    var letc := sorted[|sorted| - 1];
    var a := 0;
    var k := 0;
    while k < |sorted|
      decreases |sorted| - k
    {
      if sorted[k] == '!' {
        a := a + 1;
      }
      k := k + 1;
    }
    if letc == 'R' {
      r := r + a;
    } else if letc == 'B' {
      b := b + a;
    } else if letc == 'Y' {
      y := y + a;
    } else if letc == 'G' {
      g := g + a;
    }
    i := i + 1;
  }
  output := IntToString(r) + " " + IntToString(b) + " " + IntToString(y) + " " + IntToString(g);
}
