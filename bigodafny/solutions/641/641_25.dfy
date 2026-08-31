// 299_B. Ksusha the Squirrel  (problem 641, solution 641_25)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = input().split()
// n = int(n)
// k = int(k)
// a = list(input())
// i = 0
// j = []
// while i < n:
//     if a[i] == ".":
//         j.append(i)
//     i += 1
// h = []
// j.sort()
// f = 0
// while f < len(j) - 1:
//     h.append(-j[f] + j[f+1] - 1)
//     f += 1
// h.sort()
// if h.pop() >= k:
//     print("NO")
// else:
//     print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  var j: seq<int> := [];
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] == '.' {
      j := j + [i];
    }
    i := i + 1;
  }
  var maxGap := -1;
  var f := 0;
  while f + 1 < |j|
    decreases |j| - f
  {
    var gap := j[f+1] - j[f] - 1;
    if gap > maxGap { maxGap := gap; }
    f := f + 1;
  }
  if maxGap >= m {
    output := "NO";
  } else {
    output := "YES";
  }
}
