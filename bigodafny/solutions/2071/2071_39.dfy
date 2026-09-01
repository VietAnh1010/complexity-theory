// 667_B. Coat of Anticubism  (problem 2071, solution 2071_39)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// s = sum(a)
// t = 0
// a.sort(reverse = True)
// for i in a :
//     t += i
//     s -= i
//     if(t >= s) :
//         break
// 
// print(t - s + 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var a := Sort(a_list, (x: int, y: int) => x > y);
  var s := SumSeq(a_list);
  var t := 0;
  var idx := 0;
  var stopped := false;
  while idx < |a| && !stopped
    decreases |a| - idx
  {
    var i := a[idx];
    t := t + i;
    s := s - i;
    if t >= s {
      stopped := true;
    }
    idx := idx + 1;
  }
  output := IntToString(t - s + 1);
}
