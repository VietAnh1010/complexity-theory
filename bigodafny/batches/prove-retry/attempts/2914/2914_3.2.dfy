// 1136_A. Nastya Is Reading a Book  (problem 2914, solution 2914_3)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// chapters = []
// 
// for _ in range(n):
//     l, r = map(int, input().split())
//     chapters.append((l, r))
// 
// k = int(input())
// 
// for i in range(len(chapters)):
//     if k >= chapters[i][0] and k <= chapters[i][1]:
//         break
// 
// print(n - i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>, value: int) returns (output: string, ghost steps: nat)
  ensures steps <= 8 * (if n > 0 then n else 0) + |output| + 10
{
  steps := 1;
  var i := 0;
  var found := false;
  while i < n && !found
    invariant 0 <= i
    invariant i <= n || i == 0
    invariant found ==> i < n
    invariant steps <= 1 + 8 * i + (if found then 8 else 0)
    decreases if found then 0 else n - i
  {
    steps := steps + 8;
    if i < |intervals| && |intervals[i]| >= 2 && value >= intervals[i][0] && value <= intervals[i][1] {
      found := true;
    } else {
      i := i + 1;
    }
  }
  steps := steps + 3;
  if !found && n > 0 {
    i := n - 1;
  }
  output := IntToString(n - i);
  IntToStringDigits(n - i);
  steps := steps + 1 + |output|;
}
