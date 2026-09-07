// 1326_A. Bad Ugly Numbers  (problem 1043, solution 1043_408)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// t = int(input())
// while t:
//     n = int(input())
//     if n >= 2:    
//         print('23',end="")
//     else: 
//         print("-1")
//     while n>2:
//         print('3',end="")
//         n -= 1
//     print(" ")
//     t -= 1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    decreases |a_list| - i
  {
    var m := a_list[i];
    if m >= 2 {
      parts := parts + ["23" + Repeat("3", (m - 2) as nat) + " \n"];
    } else {
      parts := parts + ["-1\n \n"];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
