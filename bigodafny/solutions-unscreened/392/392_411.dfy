// 1223_B. Strings Equalization  (problem 392, solution 392_411)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from sys import stdin, stdout
// from math import gcd
// input = stdin.readline
// 
// for _ in range(int(input())):
//     s = input()[:-1]
//     t = input()[:-1]
//     if set(s) & set(t):
//         print('YES')
//     else:
//         print('NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CharInString(s: string, c: char): bool
  decreases |s|
{
  if |s| == 0 then false
  else if s[0] == c then true
  else CharInString(s[1..], c)
}

function HasCommonChar(s: string, t: string): bool
  decreases |s|
{
  if |s| == 0 then false
  else if CharInString(t, s[0]) then true
  else HasCommonChar(s[1..], t)
}

method Solve(n: int, string_pairs: seq<(string, string)>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < |string_pairs|
    decreases |string_pairs| - i
  {
    if HasCommonChar(string_pairs[i].0, string_pairs[i].1) {
      lines := lines + ["YES"];
    } else {
      lines := lines + ["NO"];
    }
    i := i + 1;
  }
  output := Join(lines, "\n");
}
