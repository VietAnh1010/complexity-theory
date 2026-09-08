// 672_A. Summer Camp  (problem 1467, solution 1467_532)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// if n <= 9:
//     print(n)
// elif n <= 189:
//     num = (n - 10) / 2 + 10
//     mod = (n - 10) % 2
//     s = str(num)
//     print(s[mod])
// else:
//     num = (n - 10 - 90 * 2) / 3 + 100
//     mod = (n - 10 - 90 * 2) % 3
//     s = str(num)
//     print(s[mod])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma DigitsAtLeast1(x: int)
  requires x >= 0
  ensures |IntToString(x)| >= 1
  decreases x
{
  if x < 10 {
  } else {
    DigitsAtLeast1(x / 10);
  }
}

lemma DigitsAtLeast2(x: int)
  requires x >= 10
  ensures |IntToString(x)| >= 2
{
  DigitsAtLeast1(x / 10);
}

lemma DigitsAtLeast3(x: int)
  requires x >= 100
  ensures |IntToString(x)| >= 3
{
  DigitsAtLeast2(x / 10);
}

method Solve(N: int) returns (output: string)
  requires 1 <= N <= 1000
{
  if N <= 9 {
    output := IntToString(N);
  } else if N <= 189 {
    var num := FloorDiv(N - 10, 2) + 10;
    var mod := FloorMod(N - 10, 2);
    var s := IntToString(num);
    DigitsAtLeast2(num);
    output := [s[mod]];
  } else {
    var num := FloorDiv(N - 10 - 180, 3) + 100;
    var mod := FloorMod(N - 10 - 180, 3);
    var s := IntToString(num);
    DigitsAtLeast3(num);
    output := [s[mod]];
  }
}
