// 357_A. Group of Students  (problem 894, solution 894_3)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m = int(input())
// cs = list(map(int, input().split()))
// l, r = map(int, input().split())
// s = sum(cs)
// ps = 0
// for i, a in enumerate(cs):
//     ps += a
//     if(l <= ps <= r and l <= (s-ps) <= r):
//         print(i+2)
//         break
// else:
//     print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, x: int, y: int) returns (output: string, ghost steps: nat)
  ensures steps <= 6 * |a_list| + 4
{
  steps := 1;
  var s := 0;
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant steps <= 2 * idx + 1
    decreases |a_list| - idx
  {
    s := s + a_list[idx];
    idx := idx + 1;
    steps := steps + 2;
  }
  var ps := 0;
  var i := 0;
  var found := false;
  var ans := 0;
  while i < |a_list| && !found
    invariant 0 <= i <= |a_list|
    invariant steps <= 4 * i + 2 * |a_list| + 1
    decreases |a_list| - i
  {
    ps := ps + a_list[i];
    if x <= ps && ps <= y && x <= (s - ps) && (s - ps) <= y {
      ans := i + 2;
      found := true;
    }
    i := i + 1;
    steps := steps + 4;
  }
  if found {
    output := IntToString(ans) + "\n";
  } else {
    output := "0\n";
  }
  steps := steps + 1;
}
