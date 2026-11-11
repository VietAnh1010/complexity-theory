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

lemma Log50000()
  ensures SearchPot(50000) <= 17
{
  assert CeilLog2(1) == 0;
  assert CeilLog2(2) == 1 + CeilLog2(1);
  assert CeilLog2(4) == 1 + CeilLog2(2);
  assert CeilLog2(7) == 1 + CeilLog2(4);
  assert CeilLog2(13) == 1 + CeilLog2(7);
  assert CeilLog2(25) == 1 + CeilLog2(13);
  assert CeilLog2(49) == 1 + CeilLog2(25);
  assert CeilLog2(98) == 1 + CeilLog2(49);
  assert CeilLog2(196) == 1 + CeilLog2(98);
  assert CeilLog2(391) == 1 + CeilLog2(196);
  assert CeilLog2(782) == 1 + CeilLog2(391);
  assert CeilLog2(1563) == 1 + CeilLog2(782);
  assert CeilLog2(3125) == 1 + CeilLog2(1563);
  assert CeilLog2(6250) == 1 + CeilLog2(3125);
  assert CeilLog2(12500) == 1 + CeilLog2(6250);
  assert CeilLog2(25000) == 1 + CeilLog2(12500);
  assert CeilLog2(50000) == 1 + CeilLog2(25000);
}

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 9000000
{
  steps := 0;
  steps := steps + 5 * 50000;
  var tri: seq<int> := seq(50000, k requires 0 <= k < 50000 => (k + 1) * (k + 2) / 2);
  var idx := 0;
  var found := false;
  while idx < |tri| && !found
    invariant 0 <= idx <= |tri| == 50000
    invariant steps <= 250000 + idx * 170
    decreases |tri| - idx
  {
    steps := steps + (4 + if idx < |tri| then 1 else 0);
    steps := steps + 2;
    var target := n - tri[idx];
    var lo := 0;
    steps := steps + 2;
    var hi := |tri| - 1;
    var hitFound := false;
    ghost var s0 := steps;
    ghost var it: nat := 0;
    Log50000();
    while lo <= hi && !hitFound
      invariant 0 <= lo <= |tri|
      invariant -1 <= hi < |tri|
      invariant lo <= hi + 1
      invariant steps <= s0 + 9 * it
      invariant it + (if hitFound then 0 else SearchPot(hi - lo + 1)) <= 17
      decreases !hitFound, hi - lo + 1
    {
      steps := steps + (3 + if lo <= hi then 1 else 0);
      steps := steps + 2;
      var mid := (lo + hi) / 2;
      steps := steps + 2;
      ghost var k := hi - lo + 1;
      if tri[mid] == target {
        hitFound := true;
        assert SearchPot(k) >= 1;
        it := it + 1;
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
  }
  steps := steps + (3 + if idx < |tri| then 1 else 0);
  if found {
    output := "YES";
  } else {
    output := "NO";
  }
}

import opened Prelude
