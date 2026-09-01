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

method Solve(numbers: seq<int>) returns (output: string)
{
  var ls := new int[9];
  var idx := 0;
  while idx < 9
    decreases 9 - idx
    modifies ls
  {
    ls[idx] := 0;
    idx := idx + 1;
  }
  idx := 0;
  while idx < |numbers|
    decreases |numbers| - idx
    modifies ls
  {
    var pos := numbers[idx] - 1;
    ls[pos] := ls[pos] + 1;
    idx := idx + 1;
  }
  var x: seq<int> := [];
  idx := 0;
  while idx < 9
    decreases 9 - idx
  {
    if ls[idx] > 0 {
      x := x + [ls[idx]];
    }
    idx := idx + 1;
  }
  if x == [6] || x == [2, 4] || x == [4, 2] {
    output := "Elephant";
  } else if x == [1, 1, 4] || x == [1, 4, 1] || x == [4, 1, 1] || x == [1, 5] || x == [5, 1] {
    output := "Bear";
  } else {
    output := "Alien";
  }
}
