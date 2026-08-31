// 1003_A. Polycarp's Pockets  (problem 976, solution 976_656)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// charNum = int(input())
// numArray = input().split()
// 
// b = 0
// for x in numArray:
//     if numArray.count(x) > b:
//         b = numArray.count(x)
// print(b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  var b := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var cnt := 0;
    var j := 0;
    while j < |a_list|
      decreases |a_list| - j
    {
      if a_list[j] == a_list[i] { cnt := cnt + 1; }
      j := j + 1;
    }
    if cnt > b { b := cnt; }
    i := i + 1;
  }
  output := IntToString(b);
}
