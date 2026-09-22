// 978_B. File Name  (problem 2226, solution 2226_1222)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// string = input()
//
// counter = int()
//
// result = int()
//
// for letter in string:
// 	if letter == 'x':
// 		counter += 1
//
// 		if counter >= 3:
// 			result += 1
// 	else:
// 		counter = 0
//
// print(result)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, binary_string: string) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * |binary_string| + 3
{
  var counter := 0;
  var result := 0;
  var i := 0;
  steps := 1;
  ghost var base1 := steps;
  while i < |binary_string|
    invariant 0 <= i <= |binary_string|
    invariant steps == base1 + 4 * i
    decreases |binary_string| - i
  {
    if binary_string[i] == 'x' {
      counter := counter + 1;
      if counter >= 3 { result := result + 1; }
    } else {
      counter := 0;
    }
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(result);
  steps := steps + 1;
}
