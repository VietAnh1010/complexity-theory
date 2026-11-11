// --- Python ---------------------------------------------------------
// from math import sqrt
// k=int(input())
// n=(sqrt(8*k+1)-1)/2
// if n>int(n):
// 	print("NO")
// else:
// 	print("YES")
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 32 * (if n > 0 then n else 0) + 16
  decreases *
{
  steps := 0;
  var k := n;
  steps := steps + 2;
  var target := 8 * k + 1;
  var s := 0;
  while s * s < target
    invariant 0 <= s
    invariant s == 0 || s <= target
    invariant steps == 4 + 4 * s
    decreases target - s
  {
    SqGe(s);
    steps := steps + 3;
    steps := steps + 1;
    s := s + 1;
  }
  steps := steps + 2;
  steps := steps + 2;
  if s * s == target {
    output := "YES";
  } else {
    output := "NO";
  }
}

import opened Prelude

lemma SqGe(s: int)
  requires s >= 0
  ensures s * s >= s
{
  if s > 0 {
    assert s * s >= s * 1;
  }
}
