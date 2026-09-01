// 248_A. Cupboards  (problem 1650, solution 1650_311)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// left = []
// right = []
// 
// for i in range(n):
//     l, r = input().split()
// 
//     left.append(l)
//     right.append(r)
// 
// left_0 = left.count('0')
// left_1 = left.count('1')
// right_0 = right.count('0')
// right_1 = right.count('1')
// 
// print (min(left_0, left_1) + min(right_0, right_1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string)
{
  var left0 := 0;
  var left1 := 0;
  var right0 := 0;
  var right1 := 0;
  var i := 0;
  while i < |pairs|
    decreases |pairs| - i
  {
    if pairs[i][0] == "0" { left0 := left0 + 1; } else { left1 := left1 + 1; }
    if pairs[i][1] == "0" { right0 := right0 + 1; } else { right1 := right1 + 1; }
    i := i + 1;
  }
  var m1 := if left0 < left1 then left0 else left1;
  var m2 := if right0 < right1 then right0 else right1;
  output := IntToString(m1 + m2);
}
