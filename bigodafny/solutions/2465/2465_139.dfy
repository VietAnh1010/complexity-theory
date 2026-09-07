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

method Solve(t: int, n_list: seq<int>) returns (output: string)
  requires t >= 1
  requires |n_list| == t
  requires forall k :: 0 <= k < |n_list| ==> 0 <= n_list[k] < 0x40000000
{
  var n := t;
  var vals := n_list;
  var pref := new int[n+1];
  var suff := new int[n+1];
  pref[0] := 0;
  suff[n] := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall k :: 0 <= k <= i ==> 0 <= pref[k] < 0x1_0000_0000_0000_0000
    invariant forall k :: n - i <= k <= n ==> 0 <= suff[k] < 0x1_0000_0000_0000_0000
  {
    pref[i+1] := BitOr(pref[i], vals[i]);
    suff[n-i-1] := BitOr(suff[n-i], vals[n-i-1]);
    i := i + 1;
  }
  var bestScore := -1;
  var bestIdx := 0;
  i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant 0 <= bestIdx < n
  {
    var b := BitOr(pref[i], suff[i+1]);
    var score := BitOr(vals[i], b) - b;
    if score >= bestScore {
      bestScore := score;
      bestIdx := i;
    }
    i := i + 1;
  }
  var parts := new string[n];
  parts[0] := IntToString(vals[bestIdx]);
  var j := 0;
  var pos := 1;
  while j < n
    invariant 0 <= j <= n
    invariant pos == j + 1 - (if bestIdx < j then 1 else 0)
  {
    if j != bestIdx {
      parts[pos] := IntToString(vals[j]);
      pos := pos + 1;
    }
    j := j + 1;
  }
  output := Join(parts[..], " ") + "\n";
}
