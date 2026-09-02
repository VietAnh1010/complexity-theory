// 155_A. I_love_%username%  (problem 1756, solution 1756_577)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// a = list(map(int, input().split()))
// c = 0
// for i in range(1, t):
//     if min(a[:i]) > a[i] or max(a[:i]) < a[i]: c += 1 
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var c := 0;
  var i := 1;
  while i < n
    decreases n - i
  {
    var prefix := numbers[0..i];
    if MinSeq(prefix) > numbers[i] || MaxSeq(prefix) < numbers[i] {
      c := c + 1;
    }
    i := i + 1;
  }
  output := IntToString(c);
}
