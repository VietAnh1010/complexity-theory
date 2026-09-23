// 918_A. Eleven  (problem 1699, solution 1699_98)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
//
// n=int(input())
// l=[1,1]
// b=""
// for i in range(2,n+1):
// 	l.append(l[i-2]+l[i-1])
// for j in range(1,n+1):
// 	if j in l:
// 		b+="O"
// 	else:
// 		b+="o"
// print(b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 4 * n * n + 16 * n + 6
{
  var l := [1, 1];
  var i := 2;
  steps := 2;
  ghost var base1 := steps;
  while i <= n
    invariant 2 <= i <= n + 2
    invariant |l| == i
    invariant steps <= base1 + 3 * (i - 2)
    decreases n - i + 1
  {
    l := l + [l[i - 2] + l[i - 1]];
    i := i + 1;
    steps := steps + 3;
  }
  assert |l| <= n + 2;
  var parts: seq<string> := [];
  var j := 1;
  ghost var base2 := steps;
  ghost var outer := 0;
  while j <= n
    invariant 1 <= j <= n + 1
    invariant outer == j - 1
    invariant |parts| == outer
    invariant |l| <= n + 2
    invariant steps <= base2 + (4 * (n + 2) + 3) * outer
    decreases n - j + 1
  {
    var found := false;
    var k := 0;
    ghost var base3 := steps;
    while k < |l|
      invariant 0 <= k <= |l|
      invariant steps <= base3 + 4 * k
      decreases |l| - k
    {
      if l[k] == j {
        found := true;
      }
      k := k + 1;
      steps := steps + 4;
    }
    if found {
      parts := parts + ["O"];
    } else {
      parts := parts + ["o"];
    }
    j := j + 1;
    outer := outer + 1;
    steps := steps + 3;
  }
  assert outer == n;
  NSquareBound(n);
  output := Join(parts, "");
  steps := steps + |parts| + 2;
}

lemma NSquareBound(n: int)
  requires n >= 0
  ensures (4 * (n + 2) + 3) * n == 4 * n * n + 11 * n
{
}
