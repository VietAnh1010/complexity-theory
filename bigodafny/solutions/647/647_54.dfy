// 859_C. Pie Rules  (problem 647, solution 647_54)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// x = s = 0
// for ai in reversed(a):
//     x = max(x, ai + s - x)
//     s += ai
// 
// print(s - x, x)
// 
// 
// 
// 
// # Made By Mostafa_Khaled
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var x := 0;
  var s := 0;
  var i := |a_list| - 1;
  while i >= 0
    decreases i
  {
    var ai := a_list[i];
    var candidate := ai + s - x;
    if candidate > x { x := candidate; }
    s := s + ai;
    i := i - 1;
  }
  output := IntToString(s - x) + " " + IntToString(x);
}
