// 127_B. Canvas Frames  (problem 659, solution 659_55)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = input()
// a = a.split()
// dic = {}
// for i in a:
//     dic[i] = dic.get(i, 0) + 1
// c = 0
// for v in dic.values():
//     c += v//2
// print(c//2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, ratings: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
