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

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
