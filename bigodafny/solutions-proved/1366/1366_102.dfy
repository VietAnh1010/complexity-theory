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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * NLogN(|a_list|) + 26 * |a_list| + 20 + |output|
{
  steps := 1;
  var p: seq<int> := [];
  var neg: seq<int> := [];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant |p| <= i
    invariant steps <= 1 + 6 * i
    decreases |a_list| - i
  {
    if a_list[i] > 0 { p := p + [a_list[i]]; }
    i := i + 1;
    steps := steps + 6;
  }
  i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant |p| <= |a_list| && |neg| <= i
    invariant steps <= 1 + 6 * |a_list| + 6 * i
    decreases |a_list| - i
  {
    if a_list[i] < 0 { neg := neg + [a_list[i]]; }
    i := i + 1;
    steps := steps + 6;
  }
  var s := SumSeq(p);
  steps := steps + |p| + 3;
  if FloorMod(s, 2) == 1 {
    output := IntToString(s);
    IntToStringDigits(s);
    steps := steps + Digits(s);
  } else {
    var m := -10000000;
    var sn := SortInts(neg);
    steps := steps + SortCost(|neg|);
    SortCostWithin(|neg|, |a_list|);
    SortIntsKeepsElems(neg);
    // sorted(n)[::-1]: walk the sorted list from the end
    var j := |sn|;
    while j > 0
      invariant 0 <= j <= |sn|
      invariant |sn| <= |a_list|
      invariant steps <= 1 + 13 * |a_list| + 3 + 2 * NLogN(|a_list|) + 1 + 5 * (|sn| - j)
      decreases j
    {
      var x := sn[j - 1];
      steps := steps + 5;
      if FloorMod(x, 2) == 1 {
        m := x;
        break;
      }
      j := j - 1;
    }
    var sp := SortInts(p);
    steps := steps + SortCost(|p|);
    SortCostWithin(|p|, |a_list|);
    j := 0;
    while j < |sp|
      invariant 0 <= j <= |sp|
      invariant |sp| <= |a_list|
      invariant steps <= 1 + 13 * |a_list| + 3 + 2 * NLogN(|a_list|) + 1 + 5 * |a_list| + 2 * NLogN(|a_list|) + 1 + 6 * j
      decreases |sp| - j
    {
      var y := sp[j];
      steps := steps + 6;
      if FloorMod(y, 2) == 1 && -y > m {
        m := -y;
      }
      j := j + 1;
    }
    output := IntToString(s + m);
    IntToStringDigits(s + m);
    steps := steps + 1 + Digits(s + m);
  }
}
