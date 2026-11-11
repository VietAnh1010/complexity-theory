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

include "../../../../prelude.dfy"

method Solve(n: int, intervals: seq<seq<int>>, value: int)
    returns (output: string, ghost steps: nat)
    ensures steps <= 19 * (if n > 0 then n else 0) + 9 + |output|
{
  steps := 0;
  var i := 0;
  var found := false;
  while i < n && !found
    invariant 0 <= i
    invariant i <= (if n > 0 then n else 0)
    invariant steps <= 19 * i
    decreases if found then 0 else n - i
  {
    steps := steps + (3 + if i < n then 1 else 0);
    steps := steps + (5 + (if i < |intervals| then 3 else 0) + (if i < |intervals| && |intervals[i]| >= 2 then 3 else 0) + if i < |intervals| && |intervals[i]| >= 2 && value >= intervals[i][0] then 3 else 0);
    if i < |intervals| && |intervals[i]| >= 2 && value >= intervals[i][0] && value <= intervals[i][1] {
      found := true;
    } else {
      steps := steps + 1;
      i := i + 1;
    }
  }
  steps := steps + (2 + if i < n then 1 else 0);
  steps := steps + (2 + if !found then 1 else 0);
  if !found && n > 0 {
    steps := steps + 1;
    i := n - 1;
  }
  steps := steps + (1 + Digits(n - i));
  output := IntToString(n - i);
  IntToStringDigits(n - i);
}

import opened Prelude
