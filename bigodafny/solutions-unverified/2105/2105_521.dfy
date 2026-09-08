// 1138_A. Sushi for Two  (problem 2105, solution 2105_521)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// b = []; k = 0; c = a[0]
// for i in range(n):
//     if a[i] == c: k += 1
//     else:
//         b.append(k)
//         k = 1
//         c = a[i]
// b.append(k)
// ans = []
// for i in range(len(b)-1):
//     ans.append(min(b[i], b[i+1]))
// print(max(ans)*2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: int, v_1: string) returns (output: string)
  requires v_0 >= 1
  requires |ParseInts(SplitWs(v_1))| == v_0
  requires exists k :: 0 <= k < v_0 && ParseInts(SplitWs(v_1))[k] == 1
  requires exists k :: 0 <= k < v_0 && ParseInts(SplitWs(v_1))[k] == 2
{
  var n := v_0;
  var a := ParseInts(SplitWs(v_1));
  var b: seq<int> := [];
  var k := 0;
  var c := a[0];
  var i := 0;
  assert exists p :: 0 <= p < n && a[p] != a[0] by {
    if a[0] == 1 {
      var k2 :| 0 <= k2 < n && ParseInts(SplitWs(v_1))[k2] == 2;
      assert a[k2] == ParseInts(SplitWs(v_1))[k2];
    } else {
      var k1 :| 0 <= k1 < n && ParseInts(SplitWs(v_1))[k1] == 1;
      assert a[k1] == ParseInts(SplitWs(v_1))[k1];
    }
  }
  while i < n
    invariant 0 <= i <= n
    invariant |b| >= 1 || c == a[0]
    invariant |b| >= 1 || (forall j :: 0 <= j < i ==> a[j] == a[0])
    decreases n - i
  {
    if a[i] == c {
      k := k + 1;
    } else {
      b := b + [k];
      k := 1;
      c := a[i];
    }
    i := i + 1;
  }
  b := b + [k];
  assert |b| >= 2;
  var ans: seq<int> := [];
  var j := 0;
  while j < |b| - 1
    invariant 0 <= j <= |b| - 1
    invariant |ans| == j
    decreases |b| - 1 - j
  {
    var m := if b[j] < b[j+1] then b[j] else b[j+1];
    ans := ans + [m];
    j := j + 1;
  }
  assert |ans| >= 1;
  output := IntToString(MaxSeq(ans) * 2);
}
