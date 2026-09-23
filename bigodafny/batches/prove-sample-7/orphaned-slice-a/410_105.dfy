// 725_A. Jumping Ball  (problem 410, solution 410_105)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// s = input()
//
// begin = True
// counter = 0
// ans = 0
//
// for i in range(n):
//     if begin and s[i] == "<":
//         ans += 1
//     elif s[i] == ">":
//         counter += 1
//         begin = False
//     else:
//         counter = 0
// print(ans + counter)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, arrows: string) returns (output: string, ghost steps: nat)
  requires 0 <= n <= |arrows|
  ensures steps <= 4 * n + 3
{
  var begin := true;
  var counter := 0;
  var ans := 0;
  var i := 0;
  steps := 1;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 1 + 4 * i
    decreases n - i
  {
    if begin && arrows[i] == '<' {
      ans := ans + 1;
    } else if arrows[i] == '>' {
      counter := counter + 1;
      begin := false;
    } else {
      counter := 0;
    }
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(ans + counter);
  steps := steps + 1;
}
