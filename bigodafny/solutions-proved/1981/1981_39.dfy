// p03938 AtCoder Grand Contest 007 - Construct Sequences  (problem 1981, solution 1981_39)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// p = list(map(int, input().split()))
//
// a = [i*40000+1 for i in range(n)]
// b = a[:]
// b.reverse()
//
// for i in range(n):
//     b[p[i]-1] += i+1
// print(*a)
// print(*b)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |a_list| == n
  // Python wraps a negative subscript; 152 occur across the stored tests.
  requires forall k :: 0 <= k < n ==> -n <= a_list[k] - 1 < n
  ensures steps <= 8 * n + 3
{
  steps := 1;
  var a := seq(n, i requires 0 <= i < n => i*40000+1);
  var b := seq(n, i requires 0 <= i < n => a[n-1-i]);
  steps := steps + 2 * n;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |b| == n
    invariant steps <= 4 * i + 2 * n + 1
    decreases n - i
  {
    var idx := PyIndex(a_list[i] - 1, |b|);
    b := b[idx := b[idx] + (i+1)];
    i := i + 1;
    steps := steps + 4;
  }
  output := JoinInts(a, " ") + "\n" + JoinInts(b, " ") + "\n";
  steps := steps + |a| + |b| + 2;
}
