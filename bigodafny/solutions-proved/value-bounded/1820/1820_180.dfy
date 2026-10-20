// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
// 1199_A. City Day  (problem 1820, solution 1820_180)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n , x , y = map(int,input().split())
// arr = list(map(int,input().split()))
//
// for i in range(n):
//     if i >= x :
//         if arr[i] == min(arr[i - x : i + y + 1]):
//             print(i + 1 )
//             break
//     else:
//         if arr[i] == min(arr[0 : i + y +1]):
//             print(i + 1 )
//             break
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

lemma DigitsLe(x: int)
  requires x >= 1
  ensures Digits(x) <= x
{ if x >= 10 { DigitsLe(x / 10); } }

lemma Mono(p: int, q: int, k: int)
  requires 0 <= p <= q && k >= 0
  ensures p * k <= q * k
{}

lemma Dist(n: int, k: int)
  ensures n * (k + 1) == n * k + n
{}

lemma Step(p: int, k: int)
  ensures (p + 1) * k == p * k + k
{}

method Solve(a: int, b: int, c: int, d_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires a <= |d_list|
  requires b >= 0
  requires c >= 0
  ensures steps <= (if a <= 0 then 3 else a * (18 + b + c) + 3)
{
  steps := 0;
  var n := a;
  var x := b;
  var y := c;
  var arr := d_list;
  var i := 0;
  var found := false;
  var result := 0;
  while i < n && !found
    invariant 0 <= i
    invariant n <= 0 ==> i == 0 && !found
    invariant !found ==> i <= n || n < 0
    invariant steps <= (i + (if found then 1 else 0)) * (17 + x + y)
    invariant found ==> 1 <= result <= n && result == i + 1 && i < n
    decreases !found, n - i
  {
    steps := steps + (3 + if i < n then 1 else 0);
    steps := steps + (2 + if i >= x then 1 else 0);
    var lo := if i >= x then i - x else 0;
    steps := steps + 2;
    var hi := i + y + 1;
    steps := steps + 2;
    if hi > |arr| {
      steps := steps + 1;
      hi := |arr|;
    }
    assert lo <= i;
    assert hi >= i + 1;
    steps := steps + (1 + |arr[lo .. hi]|);
    assert hi - lo <= x + y + 1;
    Step(i, 17 + x + y);
    var m := MinSeq(arr[lo .. hi]);
    steps := steps + 2;
    if arr[i] == m {
      steps := steps + 1;
      result := i + 1;
      found := true;
    } else {
      steps := steps + 1;
      i := i + 1;
    }
  }
  steps := steps + (2 + if i < n then 1 else 0);
  if n > 0 { Mono(i + (if found then 1 else 0), n, 17 + x + y); Dist(n, 17 + x + y); }
  if found {
    DigitsLe(result);
    steps := steps + Digits(result);
    output := IntToString(result);
  } else {
    output := "";
  }
}

