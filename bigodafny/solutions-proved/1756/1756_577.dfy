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

// Label O(n**2) -- agrees, and the quadratic term is real work, not an artifact
// of the translation. Iteration i takes the prefix numbers[0..i] (a copy of
// length i) and runs MinSeq and MaxSeq over it (one recursion level each per
// element), so the body costs 3i and the total is quadratic. The Python is the
// same shape: min(a[:i]) and max(a[:i]) inside the loop.
method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires n <= |numbers|
  ensures steps <= 3 * n * n + 4 * n + 7   // +7, not +3: n may be negative here
                                            // and 3n²+4n+c dips to c-1 at n = -1
{
  steps := 1;
  var c := 0;
  var i := 1;
  while i < n
    invariant 1 <= i
    invariant i > 1 ==> i <= n
    invariant steps <= 3 * i * i + 4 * i - 6
    decreases n - i
  {
    ghost var i0 := i;
    var prefix := numbers[0..i];
    if MinSeq(prefix) > numbers[i] || MaxSeq(prefix) < numbers[i] {
      c := c + 1;
    }
    i := i + 1;
    steps := steps + 3 * |prefix| + 4;
    assert |prefix| == i0;
    assert 3 * (i0 + 1) * (i0 + 1) + 4 * (i0 + 1) - 6
        == 3 * i0 * i0 + 4 * i0 - 6 + 3 * i0 + 4 + (3 * i0 + 3);
  }
  output := IntToString(c);
  steps := steps + 2;
}
