// 797_B. Odd sum  (problem 1366, solution 1366_102)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// '''input
// 10
// 1184 5136 1654 3254 6576 6900 6468 327 179 7114
// '''
// input()
// a = list(map(int, input().split()))
// s = 0
// p, n = [i for i in a if i > 0], [j for j in a if j < 0]
// s = sum(p)
// if s % 2 == 1:
// 	print(s)
// else:
// 	m = -10000000
// 	for x in sorted(n)[::-1]:
// 		if x % 2 == 1:
// 			m = x
// 			break
// 	for y in sorted(p):
// 		if y % 2 == 1:
// 			m = max(m, -y)
// 	print(s + m)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var s := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    if a_list[i] > 0 { s := s + a_list[i]; }
    i := i + 1;
  }
  if FloorMod(s, 2) == 1 {
    output := IntToString(s);
  } else {
    // sorted(n)[::-1] scanned for first odd == max odd negative (order-independent).
    var m := -10000000;
    var j := 0;
    while j < |a_list|
      decreases |a_list| - j
    {
      if a_list[j] < 0 && FloorMod(a_list[j], 2) == 1 && a_list[j] > m {
        m := a_list[j];
      }
      j := j + 1;
    }
    j := 0;
    while j < |a_list|
      decreases |a_list| - j
    {
      if a_list[j] > 0 && FloorMod(a_list[j], 2) == 1 && -a_list[j] > m {
        m := -a_list[j];
      }
      j := j + 1;
    }
    output := IntToString(s + m);
  }
}
