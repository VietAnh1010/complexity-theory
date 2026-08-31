// 1113_B. Sasha and Magnetic Machines  (problem 342, solution 342_86)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// input()
// a = list(map(int , input().split()))
// m = min(a)
// print(sum(a)-max(i+m-i//j-m*j for i in set(a)
// for j in range(1 , int(i**.5) + 1)if i%j==0))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var total := 0;
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    total := total + a_list[idx];
    idx := idx + 1;
  }
  var m := a_list[0];
  idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    if a_list[idx] < m { m := a_list[idx]; }
    idx := idx + 1;
  }
  var diff := 0;
  idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    var v := a_list[idx];
    var j := 1;
    while j * j <= v
      decreases v - j * j
    {
      if v % j == 0 {
        var term := v + m - v / j - m * j;
        if term > diff { diff := term; }
      }
      j := j + 1;
    }
    idx := idx + 1;
  }
  output := IntToString(total - diff);
}
