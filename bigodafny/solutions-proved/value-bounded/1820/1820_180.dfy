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

// Isolated multiplication: (i+1)*K == i*K + K.
lemma MulDistribAdd(i: int, K: int)
  ensures (i + 1) * K == i * K + K
{}

// Isolated monotonicity: a <= b, c >= 0 ==> c*a <= c*b.
lemma MulMonoLeft(a: int, b: int, c: int)
  requires a <= b
  requires c >= 0
  ensures c * a <= c * b
{}

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string, ghost steps: nat)
  requires a <= |d_list|
  requires b >= 0
  requires c >= 0
  ensures steps <= 2 + (|d_list| + 4) * (|d_list| + 2)
{
  steps := 1;
  var n := a;
  var x := b;
  var y := c;
  var arr := d_list;
  var i := 0;
  var found := false;
  var result := 0;
  ghost var cnt := 0;
  while i < n && !found
    invariant 0 <= i
    invariant i <= |d_list|
    invariant cnt <= i + (if found then 2 else 1)
    invariant steps <= 1 + (|d_list| + 4) * cnt
    decreases !found, n - i
  {
    var lo := if i >= x then i - x else 0;
    var hi := i + y + 1;
    if hi > |arr| { hi := |arr|; }
    assert lo <= i;
    assert hi >= i + 1;
    var window := arr[lo..hi];
    var m := MinSeq(window);
    steps := steps + 1 + |window| + 2;
    ghost var cntOld := cnt;
    cnt := cnt + 1;
    assert cnt * (|d_list| + 4) == cntOld * (|d_list| + 4) + (|d_list| + 4)
      by { MulDistribAdd(cntOld, |d_list| + 4); }
    if arr[i] == m {
      result := i + 1;
      found := true;
    } else {
      i := i + 1;
    }
  }
  assert cnt <= i + 2;
  assert (|d_list| + 4) * cnt <= (|d_list| + 4) * (i + 2)
    by { MulMonoLeft(cnt, i + 2, |d_list| + 4); }
  assert (|d_list| + 4) * (i + 2) <= (|d_list| + 4) * (|d_list| + 2)
    by { MulMonoLeft(i + 2, |d_list| + 2, |d_list| + 4); }
  if found {
    output := IntToString(result);
  } else {
    output := "";
  }
  steps := steps + 1;
}
