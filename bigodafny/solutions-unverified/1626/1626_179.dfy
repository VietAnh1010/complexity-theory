// 348_A. Mafia  (problem 1626, solution 1626_179)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// n = int(input())
// a = [int(x) for x in input().split()]
// a.sort(reverse=True)
// low = a[0]
// high = sum(a)
// while low < high:
// 	mid = (low + high) // 2
// 	t = 0
// 	i = 0
// 	while i < n and t < mid:
// 		if t >= a[i]:
// 			t = mid
// 			break
// 		t += (mid - a[i])
// 		i += 1
// 	if t >= mid:
// 		high = mid
// 	else:
// 		low = mid + 1
// print(high)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var a := Sort(a_list, (x: int, y: int) => x > y);
  var low := a[0];
  var high := SumSeq(a);
  while low < high
    decreases high - low
  {
    var mid := (low + high) / 2;
    var t := 0;
    var i := 0;
    var brk := false;
    while i < n && t < mid && !brk
      decreases n - i
    {
      if t >= a[i] {
        t := mid;
        brk := true;
      } else {
        t := t + (mid - a[i]);
        i := i + 1;
      }
    }
    if t >= mid {
      high := mid;
    } else {
      low := mid + 1;
    }
  }
  output := IntToString(high);
}
