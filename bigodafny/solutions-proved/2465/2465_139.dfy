// 1299_A. Anu Has a Function  (problem 2465, solution 2465_139)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// vals = list(map(int, input().split()))
// pref, suff = [0] * (n + 1), [0] * (n + 1)
// for i in range(n):
//     pref[i + 1] = pref[i] | vals[i]
//     suff[n - i - 1] = suff[n - i] | vals[n - i - 1]
// ret = (-float('inf'), -float('inf'))
// for i, a in enumerate(vals):
//     b = pref[i] | suff[i + 1]
//     ret = max(ret, ((a | b) - b, i))
// print(*[vals[ret[1]]] + [v for i, v in enumerate(vals) if i != ret[1]])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(t: int, n_list: seq<int>) returns (output: string, ghost steps: nat)
  requires t >= 1
  requires |n_list| == t
  requires forall k :: 0 <= k < |n_list| ==> 0 <= n_list[k] < 0x40000000
  ensures steps <= 30 * t + 10
{
  steps := 1;
  var n := t;
  var vals := n_list;
  var pref := seq(n+1, _ => 0);
  var suff := seq(n+1, _ => 0);
  pref := pref[0 := 0];
  suff := suff[n := 0];
  steps := steps + 3;
  var i := 0;
  ghost var b1 := steps;
  while i < n
    invariant 0 <= i <= n
    invariant |pref| == n + 1 && |suff| == n + 1
    invariant forall k :: 0 <= k <= i ==> 0 <= pref[k] < 0x1_0000_0000_0000_0000
    invariant forall k :: n - i <= k <= n ==> 0 <= suff[k] < 0x1_0000_0000_0000_0000
    invariant steps <= b1 + 6 * i
    decreases n - i
  {
    pref := pref[i+1 := BitOr(pref[i], vals[i])];
    suff := suff[n-i-1 := BitOr(suff[n-i], vals[n-i-1])];
    i := i + 1;
    steps := steps + 6;
  }
  var bestScore := -1;
  var bestIdx := 0;
  i := 0;
  ghost var b2 := steps;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= bestIdx < n
    invariant |pref| == n + 1 && |suff| == n + 1
    invariant steps <= b2 + 5 * i
    decreases n - i
  {
    var b := BitOr(pref[i], suff[i+1]);
    var score := BitOr(vals[i], b) - b;
    if score >= bestScore {
      bestScore := score;
      bestIdx := i;
    }
    i := i + 1;
    steps := steps + 5;
  }
  var parts := seq(n, _ => "");
  parts := parts[0 := IntToString(vals[bestIdx])];
  steps := steps + 2;
  var j := 0;
  var pos := 1;
  ghost var b3 := steps;
  while j < n
    invariant 0 <= j <= n
    invariant pos == j + 1 - (if bestIdx < j then 1 else 0)
    invariant |parts| == n
    invariant steps <= b3 + 4 * j
    decreases n - j
  {
    if j != bestIdx {
      parts := parts[pos := IntToString(vals[j])];
      pos := pos + 1;
    }
    j := j + 1;
    steps := steps + 4;
  }
  output := Join(parts, " ") + "\n";
  steps := steps + 12 * n + 2; // Join charge: each part is IntToString of a
                                // value < 2^30, so at most 10 digits; SumLen(parts)
                                // <= 10n, plus |parts| = n for the Join charge itself.
}
