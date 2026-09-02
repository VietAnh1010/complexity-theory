// 1032_A. Kitchen Utensils  (problem 138, solution 138_360)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// arr = list(map(int, input().split()))
// 
// curMax = 0
// maps = {}
// for a in arr:
//     if a not in maps:
//         maps[a] = 1
//     else:
//         maps[a] += 1
//     curMax = max(curMax, maps[a])
// 
// if curMax % k != 0:
//     curMax = curMax - (curMax % k) + k
// 
// print (curMax * len(maps) - len(arr))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string)
{
  var sorted := SortInts(numbers);
  var m := |sorted|;
  var curMax := 0;
  var distinct := 0;
  var i := 0;
  while i < m
    decreases m - i
  {
    var j := i;
    while j < m && sorted[j] == sorted[i]
      decreases m - j
    {
      j := j + 1;
    }
    var cnt := j - i;
    if cnt > curMax {
      curMax := cnt;
    }
    distinct := distinct + 1;
    i := j;
  }
  if curMax % k != 0 {
    curMax := curMax - (curMax % k) + k;
  }
  var result := curMax * distinct - |numbers|;
  output := IntToString(result);
}
