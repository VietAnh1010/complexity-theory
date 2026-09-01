// 914_A. Perfect Squares  (problem 2358, solution 2358_421)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// input()
// ar = list(map(int, input().split()))
// 
// maxim = -10 ** 6
// 
// for i in ar:
//     if (i < 0 or (int(i ** 0.5)) ** 2 != i) and i > maxim:
//         maxim = i
// 
// print(maxim)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var maxim := -1000000;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var v := a_list[i];
    var notSquare := true;
    if v >= 0 {
      var r := IntSqrt2358b(v);
      notSquare := r * r != v;
    }
    if (v < 0 || notSquare) && v > maxim {
      maxim := v;
    }
    i := i + 1;
  }
  output := IntToString(maxim);
}

method IntSqrt2358b(x: int) returns (r: int)
{
  r := 0;
  while (r + 1) * (r + 1) <= x
    decreases x - r
  {
    r := r + 1;
  }
}
