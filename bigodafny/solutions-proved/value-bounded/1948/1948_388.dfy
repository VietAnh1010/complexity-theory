// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   One input number, label O(1), and a `while s*s < target` search that runs
//   about sqrt(8n+1) times. The proved bound 32 * n + 5 is linear in the
//   VALUE -- loose against the algorithm's sqrt, decisive against the label,
//   which cannot hold.
//
//   This row was this project's textbook value-to-size example and sat in
//   batches/value-bounded-open/ from prove-sample-4 until prove-sample-6
//   closed it on the third attempt.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
// 47_A. Triangular numbers  (problem 1948, solution 1948_388)
// time complexity: O(1)
// python exact-diff baseline: exact

include "../../../prelude.dfy"
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
