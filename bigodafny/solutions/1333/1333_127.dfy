// 1029_C. Maximal Intersection  (problem 1333, solution 1333_127)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// L = []
// R = []
// S = []
// for _ in range(n):
//     a,b = [int(x) for x in input().split()]
//     L.append(a)
//     R.append(b)
//     S.append((a,b))
// 
// 
// L.sort(reverse = True)
// R.sort()
// 
// if (L[0],R[0]) in S:
//     print(max(R[1]-L[1],0))
// else:
//     print(max(R[0]-L[1],R[1]-L[0],0))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>) returns (output: string)
{
{

  var L := seq(n, idx requires 0 <= idx < n => intervals[idx][0]);
  var R := seq(n, idx requires 0 <= idx < n => intervals[idx][1]);
  var Ldesc := Sort(L, (x: int, y: int) => x > y);
  var Rasc := SortInts(R);
  var found := false;
  var idx2 := 0;
  while idx2 < n
    decreases n - idx2
  {
    if intervals[idx2][0] == Ldesc[0] && intervals[idx2][1] == Rasc[0] {
      found := true;
    }
    idx2 := idx2 + 1;
  }
  var ans := 0;
  if found {
    var v := Rasc[1] - Ldesc[1];
    ans := if v > 0 then v else 0;
  } else {
    var v1 := Rasc[0] - Ldesc[1];
    var v2 := Rasc[1] - Ldesc[0];
    var mx := if v1 > v2 then v1 else v2;
    ans := if mx > 0 then mx else 0;
  }
  output := IntToString(ans);
}
}
