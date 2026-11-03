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

include "../../../../prelude.dfy"

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 50000 * (9 * SearchPot(50000) + 21) + 250010
{
  steps := 0;
  steps := steps + 5 * 50000;
  var tri: seq<int> := seq(50000, k requires 0 <= k < 50000 => (k + 1) * (k + 2) / 2);
  var idx := 0;
  var found := false;
  ghost var K := 9 * SearchPot(50000) + 21;
  ghost var b0 := steps;
  while idx < |tri| && !found
    invariant 0 <= idx <= |tri|
    invariant |tri| == 50000
    invariant steps <= b0 + idx * K
    decreases |tri| - idx
  {
    ghost var s00 := steps;
    steps := steps + (4 + if idx < |tri| then 1 else 0);
    steps := steps + 2;
    var target := n - tri[idx];
    var lo := 0;
    steps := steps + 2;
    var hi := |tri| - 1;
    var hitFound := false;
    ghost var it: nat := 0;
    ghost var b1 := steps;
    while lo <= hi && !hitFound
      invariant 0 <= lo <= |tri|
      invariant -1 <= hi < |tri|
      invariant lo <= hi + 1
      invariant it + SearchPot(hi - lo + 1) <= SearchPot(50000)
      invariant steps <= b1 + 9 * it + (if hitFound then 8 else 0)
      decreases !hitFound, hi - lo + 1
    {
      ghost var k := hi - lo + 1;
      steps := steps + (3 + if lo <= hi then 1 else 0);
      steps := steps + 2;
      var mid := (lo + hi) / 2;
      steps := steps + 2;
      if tri[mid] == target {
        hitFound := true;
      } else if tri[mid] < target {
        steps := steps + 1;
        lo := mid + 1;
        BisectStep(k, hi - lo + 1);
        it := it + 1;
      } else {
        steps := steps + 1;
        hi := mid - 1;
        BisectStep(k, hi - lo + 1);
        it := it + 1;
      }
    }
    steps := steps + (2 + if lo <= hi then 1 else 0);
    if hitFound {
      found := true;
    }
    steps := steps + 1;
    idx := idx + 1;
    CostMulDistrib(idx - 1, 1, idx, K);
  }
  CostMulMonoLeft(idx, 50000, K);
  steps := steps + (3 + if idx < |tri| then 1 else 0);
  if found {
    output := "YES";
  } else {
    output := "NO";
  }
}

import opened Prelude
