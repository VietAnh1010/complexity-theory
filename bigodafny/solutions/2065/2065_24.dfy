// 192_A. Funky Numbers  (problem 2065, solution 2065_24)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// bruh = set([(i+1)*i/2 for i in range(1, 50001)])
// n = int(input())
// if any(n-t in bruh for t in bruh):
//     print('YES')
// else:
//     print('NO')
// ###### thanking telegram for solutions ######
// '''__________ ____ ___  _____________  __.___ 
// \______   \    |   \/   _____/    |/ _|   |
//  |       _/    |   /\_____  \|      < |   |
//  |    |   \    |  / /        \    |  \|   |
//  |____|_  /______/ /_______  /____|__ \___|
// '''
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var tri: seq<int> := seq(50000, k requires 0 <= k < 50000 => (k + 1) * (k + 2) / 2);
  var idx := 0;
  var found := false;
  while idx < |tri| && !found
    decreases |tri| - idx
  {
    var target := n - tri[idx];
    var lo := 0;
    var hi := |tri| - 1;
    var hitFound := false;
    while lo <= hi && !hitFound
      decreases hi - lo + 1
    {
      var mid := (lo + hi) / 2;
      if tri[mid] == target {
        hitFound := true;
      } else if tri[mid] < target {
        lo := mid + 1;
      } else {
        hi := mid - 1;
      }
    }
    if hitFound {
      found := true;
    }
    idx := idx + 1;
  }
  if found {
    output := "YES";
  } else {
    output := "NO";
  }
}
