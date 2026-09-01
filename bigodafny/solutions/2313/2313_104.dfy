// p02994 AtCoder Beginner Contest 131 - Bite Eating  (problem 2313, solution 2313_104)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, l = map(int, input().split())
// s = [0] * n
// for i in range(n):
//     s[i] = i + l
// s.sort(key=abs)
// print(sum(s[1:]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string)
{
  var n := a;
  var l := b;
  var s: seq<int> := seq(n, i requires 0 <= i < n => i + l);
  var sorted := Sort(s, (x: int, y: int) => AbsInt(x) < AbsInt(y));
  var total := SumSeq(sorted[1..]);
  output := IntToString(total);
}
