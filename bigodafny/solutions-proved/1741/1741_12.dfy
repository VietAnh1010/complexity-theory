// p03072 AtCoder Beginner Contest 124 - Great Ocean View  (problem 1741, solution 1741_12)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// h = list(map(int,input().split()))
// c = 0
// for i in range(n):
//     if h[i]>=max(h[:i+1]):
//         c+=1
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, scores: seq<int>) returns (output: string, ghost steps: nat)
  requires |scores| == n
  ensures steps <= n * n + 8 * n + 1 + |output|
{
  steps := 1;
  var c := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 1 + i * (n + 8)
    decreases n - i
  {
    var mx := MaxSeq(scores[0..i + 1]);
    steps := steps + 1 + (i + 1);
    if scores[i] >= mx {
      c := c + 1;
    }
    i := i + 1;
    steps := steps + 6;
    assert i * (n + 8) == (i - 1) * (n + 8) + n + 8;
  }
  output := IntToString(c);
  IntToStringDigits(c);
  steps := steps + Digits(c);
}
