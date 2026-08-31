// 390_A. Inna and Alarm Clock  (problem 225, solution 225_85)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// x = set()
// y = set()
// for i in range(n):
//     a, b = map(int, input().split())
//     x.add(a)
//     y.add(b)
// print(min(len(x), len(y)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<seq<int>>) returns (output: string)
{
  var xs: set<int> := {};
  var ys: set<int> := {};
  var i := 0;
  while i < n
    decreases n - i
  {
    xs := xs + {coordinates[i][0]};
    ys := ys + {coordinates[i][1]};
    i := i + 1;
  }
  var sx := |xs|;
  var sy := |ys|;
  output := IntToString(if sx <= sy then sx else sy);
}
