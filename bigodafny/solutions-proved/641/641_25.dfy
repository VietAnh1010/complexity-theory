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

method Solve(n: int, m: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * NLogN(|s|) + 14 * |s| + 12
{
  steps := 1;
  var j: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |j| <= i
    invariant steps <= 4 * i + 1
    decreases |s| - i
  {
    steps := steps + 4;
    if s[i] == '.' {
      j := j + [i];
    }
    i := i + 1;
  }
  steps := steps + SortCost(|j|);
  SortCostWithin(|j|, |s|);
  j := SortInts(j);
  var h: seq<int> := [];
  var f := 0;
  ghost var base := steps;
  while f + 1 < |j|
    invariant 0 <= f <= |j|
    invariant |h| == f
    invariant steps <= base + 5 * f
    decreases |j| - f
  {
    steps := steps + 5;
    h := h + [j[f+1] - j[f] - 1];
    f := f + 1;
  }
  steps := steps + SortCost(|h|);
  SortCostWithin(|h|, |s|);
  h := SortInts(h);
  steps := steps + 6;
  var maxGap := -1;
  if |h| > 0 {
    maxGap := h[|h| - 1];
    h := h[..|h| - 1];
  }
  if maxGap >= m {
    output := "NO";
  } else {
    output := "YES";
  }
}
