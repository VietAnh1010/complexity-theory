// p03281 AtCoder Beginner Contest 106 - 105  (problem 1254, solution 1254_187)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// x=0
// for i in range(1,n+1,2):
//     c=0
//     for j in range(1,i+1):
//         if i%j==0:
//             c+=1
//     if c==8:
//         x+=1
// print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma SqMono(a: int, b: int)
  requires 0 <= a <= b
  ensures a * a <= b * b
{
  assert (b - a) * (b + a) == b * b - a * a;
  assert (b - a) * (b + a) >= 0;
}

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 1
  ensures steps <= (n + 2) * (n + 2) + 8 * (n + 2) + 20
{
  steps := 1;
  var x := 0;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 2
    invariant steps <= i * i + 4 * i + 5
    decreases n - i
  {
    var iOld := i;
    var s0 := steps;
    var c := 0;
    var j := 1;
    while j <= i
      invariant 1 <= j <= i + 1
      invariant steps <= s0 + 2 * (j - 1)
      decreases i - j
    {
      if i % j == 0 { c := c + 1; }
      j := j + 1;
      steps := steps + 2;
    }
    if c == 8 { x := x + 1; }
    i := i + 2;
    steps := steps + 3;
    assert s0 <= iOld * iOld + 4 * iOld + 5;
    assert steps <= s0 + 2 * iOld + 3;
    assert (iOld + 2) * (iOld + 2) + 4 * (iOld + 2) + 5 == iOld * iOld + 8 * iOld + 17;
    assert i == iOld + 2;
  }
  SqMono(i, n + 2);
  output := IntToString(x);
}
