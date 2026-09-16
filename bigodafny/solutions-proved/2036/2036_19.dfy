// 471_A. MUH and Sticks  (problem 2036, solution 2036_19)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// ls = [0] * 9
// for i in input().split():
//     ls[int(i) - 1] += 1
// x = [i for i in ls if i > 0]
// if x == [6] or x == [2, 4] or x == [4, 2]:
//     print("Elephant")
// elif x == [1,1,4] or x == [1,4,1] or x == [4,1,1] or x == [1,5] or x == [5,1]:
//     print("Bear")
// else:
//     print("Alien")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(n). Two fixed-size (9) loops plus one pass over `numbers`.
method Solve(numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires forall idx :: 0 <= idx < |numbers| ==> 1 <= numbers[idx] <= 9
  ensures steps <= 2 * |numbers| + 40
{
  steps := 1;
  var ls := seq(9, _ => 0);
  var idx := 0;
  while idx < 9
    invariant |ls| == 9
    invariant 0 <= idx <= 9
    invariant steps <= 2 * idx + 1
    decreases 9 - idx
  {
    ls := ls[idx := 0];
    idx := idx + 1;
    steps := steps + 2;
  }
  idx := 0;
  while idx < |numbers|
    invariant 0 <= idx <= |numbers|
    invariant |ls| == 9
    invariant steps <= 2 * idx + 19
    decreases |numbers| - idx
  {
    var pos := numbers[idx] - 1;
    ls := ls[pos := ls[pos] + 1];
    idx := idx + 1;
    steps := steps + 2;
  }
  var x: seq<int> := [];
  idx := 0;
  while idx < 9
    invariant |ls| == 9
    invariant 0 <= idx <= 9
    invariant steps <= 2 * |numbers| + 2 * idx + 19
    decreases 9 - idx
  {
    if ls[idx] > 0 {
      x := x + [ls[idx]];
    }
    idx := idx + 1;
    steps := steps + 2;
  }
  if x == [6] || x == [2, 4] || x == [4, 2] {
    output := "Elephant";
  } else if x == [1, 1, 4] || x == [1, 4, 1] || x == [4, 1, 1] || x == [1, 5] || x == [5, 1] {
    output := "Bear";
  } else {
    output := "Alien";
  }
  steps := steps + 1;
}
