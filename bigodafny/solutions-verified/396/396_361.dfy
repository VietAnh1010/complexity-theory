// 1008_B. Turn the Rectangles  (problem 396, solution 396_361)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// dimensions = []
// flag = 1
// 
// while n > 0:
//     dimensions.append(list(map(int, input().split())))
//     n -= 1
// 
// maximum = max(dimensions[0])
// 
// for i in range(1, len(dimensions)):
//     if maximum >= max(dimensions[i]):
//         maximum = max(dimensions[i])
//         continue
//     elif maximum >= min(dimensions[i]):
//         maximum = min(dimensions[i])
//         continue
//     else:
//         flag = 0
//         break
// 
// if flag:
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(n*m). Python's `max(dimensions[i])` / `min(dimensions[i])` scan a row,
// but every row of this problem is a rectangle -- two numbers -- and the
// translation reads exactly row[0] and row[1]. The cost per row is therefore
// constant and no second dimension enters. Honest bound O(n), n = |rectangles|.
// The loop also stops at the first violating row, so this is an upper bound the
// data often beats.
method Solve(n: int, rectangles: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires |rectangles| >= 1
  requires forall k :: 0 <= k < |rectangles| ==> |rectangles[k]| >= 2
  ensures steps <= 8 * |rectangles| + 6
{
  steps := 1;
  var maxV := if rectangles[0][0] > rectangles[0][1] then rectangles[0][0] else rectangles[0][1];
  steps := steps + 3;
  var flag := true;
  var i := 1;
  while i < |rectangles| && flag
    invariant 1 <= i <= |rectangles|
    invariant steps <= 8 * i - 4
    decreases |rectangles| - i
  {
    var row := rectangles[i];
    var mx := if row[0] > row[1] then row[0] else row[1];
    var mn := if row[0] < row[1] then row[0] else row[1];
    if maxV >= mx {
      maxV := mx;
    } else if maxV >= mn {
      maxV := mn;
    } else {
      flag := false;
    }
    i := i + 1;
    steps := steps + 8;
  }
  output := if flag then "YES" else "NO";
  steps := steps + 2;
}
