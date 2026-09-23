// p02721 AtCoder Beginner Contest 161 - Yutori  (problem 1369, solution 1369_7)
// time complexity: O(n)
// python exact-diff baseline: exact

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a: int, b: int, s: string) returns (output: string, ghost steps: nat)
  requires a >= 1
  requires b >= 0
  requires n == |s|
  requires a <= n
  ensures steps <= 6 * n + 5 * a + 3
{
  steps := 1;
  var N := n;
  var K := a;
  var C := b;
  var l := seq(K, _ => 0);
  var r := seq(K, _ => 0);
  var i := 0;
  var j := 0;
  ghost var iters1 := 0;
  steps := steps + 2 * K;
  while i < N && l[K - 1] == 0
    invariant 0 <= i
    invariant |l| == K
    invariant l[K - 1] == 0 ==> 0 <= j <= K - 1
    invariant iters1 <= i
    invariant iters1 <= N
    invariant steps <= 3 * iters1 + 2 * K + 1
    decreases N - i
  {
    if s[i] == 'o' {
      l := l[j := i + 1];
      i := i + C + 1;
      j := j + 1;
    } else {
      i := i + 1;
    }
    iters1 := iters1 + 1;
    steps := steps + 3;
  }
  assert steps <= 3 * N + 2 * K + 1;
  i := 0;
  j := K - 1;
  ghost var iters2 := 0;
  while i < N && r[0] == 0
    invariant 0 <= i
    invariant |r| == K
    invariant r[0] == 0 ==> 0 <= j <= K - 1
    invariant iters2 <= i
    invariant iters2 <= N
    invariant steps <= 3 * N + 2 * K + 1 + 3 * iters2
    decreases N - i
  {
    if s[N - i - 1] == 'o' {
      r := r[j := N - i];
      i := i + C + 1;
      j := j - 1;
    } else {
      i := i + 1;
    }
    iters2 := iters2 + 1;
    steps := steps + 3;
  }
  assert steps <= 6 * N + 2 * K + 1;
  var parts: seq<string> := [];
  var k := 0;
  while k < K
    invariant 0 <= k <= K
    invariant |r| == K
    invariant |l| == K
    invariant |parts| <= k
    invariant steps <= 6 * N + 2 * K + 1 + 2 * k
    decreases K - k
  {
    if r[k] == l[k] {
      parts := parts + [IntToString(r[k])];
    }
    k := k + 1;
    steps := steps + 2;
  }
  output := Join(parts, "\n");
  steps := steps + |parts| + 1;
}
