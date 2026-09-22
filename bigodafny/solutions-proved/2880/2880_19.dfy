// 774_C. Maximum Number  (problem 2880, solution 2880_19)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a=int(input())
// sstring=[]
// if a%2:
//    sstring.append('7')
// else:
//    a=a
// if a%2:
//    a=a-3
// else:
//    a=a
// for i in range (a // 2):
//    sstring.append('1')
// print(''.join(sstring))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// n is a value here (there is no sequence input), so a loop bounded by it
// counts as its own parameter, per COMPLEXITY.md's value-vs-size convention.
method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 2 * n + 15
{
  steps := 1;
  var a := n;
  var parts: seq<string> := [];
  if a % 2 == 1 {
    parts := parts + ["7"];
  }
  steps := steps + 2;
  if a % 2 == 1 {
    a := a - 3;
  }
  steps := steps + 2;
  var raw := a / 2;
  var cnt := if raw < 0 then 0 else raw;
  steps := steps + 2;
  var i := 0;
  ghost var base1 := steps;
  ghost var partsBase := |parts|;
  while i < cnt
    invariant 0 <= i <= cnt
    invariant steps <= base1 + 2 * i
    invariant |parts| == partsBase + i
    decreases cnt - i
  {
    parts := parts + ["1"];
    i := i + 1;
    steps := steps + 2;
  }
  assert cnt <= n / 2 + 1;
  assert steps <= base1 + 2 * cnt;
  assert |parts| <= cnt + 1;
  output := Join(parts, "");
  steps := steps + |parts| + 2;
}
