// 47_A. Triangular numbers  (problem 1948, solution 1948_388)
// time complexity: O(1)
// python exact-diff baseline: exact

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 32 * n + 5
{
  steps := 1;
  var k := n;
  var target := 8 * k + 1;
  var s := 0;
  while s * s < target
    invariant 0 <= s <= target
    invariant steps <= 4 * s + 1
    decreases target - s
  {
    s := s + 1;
    steps := steps + 4;
  }
  if s * s == target {
    output := "YES";
  } else {
    output := "NO";
  }
}
