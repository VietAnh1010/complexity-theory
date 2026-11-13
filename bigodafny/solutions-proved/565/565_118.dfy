// 914_B. Conan and Agasa play a Card Game  (problem 565, solution 565_118)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from pprint import pprint as pp
// def GI(): return int(input())
// def GIS(): return map(int, input().split())
// 
// def main():
//   GI()
//   l = list(GIS())
// 
//   s = [0] * (10 ** 5 + 1)
// 
//   for x in l:
//     s[x] += 1
// 
//   for x in reversed(s):
//     if x % 2:
//       return "Conan"
// 
//   return "Agasa"
// 
// print(main())
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 6 * |numbers| + 700010
  requires forall x :: x in numbers ==> 0 <= x <= 100000
{

  steps := 1;
  var maxV := 100000;
  var s := new int[maxV + 1];
  var z := 0;
  while z <= maxV
    invariant 0 <= z <= maxV + 1
    invariant steps == 1 + 3 * z
    decreases maxV + 1 - z
  {
    steps := steps + 3;
    s[z] := 0;
    z := z + 1;
  }
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant steps == 1 + 3 * (maxV + 1) + 6 * i
    decreases |numbers| - i
  {
    steps := steps + 6;
    assert numbers[i] in numbers;
    s[numbers[i]] := s[numbers[i]] + 1;
    i := i + 1;
  }
  var found := false;
  var j := 0;
  while j <= maxV
    invariant 0 <= j <= maxV + 1
    invariant steps == 1 + 3 * (maxV + 1) + 6 * |numbers| + 4 * j
    decreases maxV + 1 - j
  {
    steps := steps + 4;
    if s[j] % 2 == 1 { found := true; }
    j := j + 1;
  }
  steps := steps + 1;
  output := if found then "Conan" else "Agasa";
}
