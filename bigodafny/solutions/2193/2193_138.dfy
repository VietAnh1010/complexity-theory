// 52_A. 123-sequence  (problem 2193, solution 2193_138)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// 
// n_nums = int(sys.stdin.readline())
// values = [int(x) for x in sys.stdin.readline().split()]
// 
// one, two, three = 0, 0, 0
// for i in values:
//     if i == 1:
//         one += 1
//     if i == 2:
//         two += 1
//     if i == 3:
//         three += 1
// 
// result = one + two + three - max(one, two, three)
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var one := 0;
  var two := 0;
  var three := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    if a_list[i] == 1 { one := one + 1; }
    if a_list[i] == 2 { two := two + 1; }
    if a_list[i] == 3 { three := three + 1; }
    i := i + 1;
  }
  var mx := MaxSeq([one, two, three]);
  output := IntToString(one + two + three - mx);
}
