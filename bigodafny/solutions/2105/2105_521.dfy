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
{
  var n := v_0;
  var a := ParseInts(SplitWs(v_1));
  var b: seq<int> := [];
  var k := 0;
  var c := a[0];
  var i := 0;
  while i < n
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
  var ans: seq<int> := [];
  var j := 0;
  while j < |b| - 1
    decreases |b| - 1 - j
  {
    var m := if b[j] < b[j+1] then b[j] else b[j+1];
    ans := ans + [m];
    j := j + 1;
  }
  output := IntToString(MaxSeq(ans) * 2);
}
