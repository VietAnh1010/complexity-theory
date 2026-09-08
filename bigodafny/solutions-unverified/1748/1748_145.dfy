// 1256_C. Platforms Jumping  (problem 1748, solution 1748_145)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n , m , d = map(int , input().split())
// array = list(map(int , input().split()))
// ss = sum(array)
// ans = [0] * (n + 1)
// s = 0
// for i in range(m) :
//     pos = min(s + d , n + 1 - ss)
//     for j in range(pos , pos + array[i]):
//         ans[j] = i + 1
//     s = pos + array[i] - 1
//     ss -= array[i]
// if s + d <= n :
//     print("NO")
// else :
//     print("YES")
//     for i in range(1 , n + 1) :
//         print(ans[i] , end=' ')
//     print("")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function Suf1748(s: seq<int>, i: nat): int
  requires i <= |s|
  decreases |s| - i
{ if i == |s| then 0 else s[i] + Suf1748(s, i + 1) }

lemma SumFromIsSuf1748(s: seq<int>, i: nat, acc: int)
  requires i <= |s|
  ensures SumFrom(s, i, acc) == acc + Suf1748(s, i)
  decreases |s| - i
{ if i < |s| { SumFromIsSuf1748(s, i + 1, acc + s[i]); } }

lemma SufNonNeg1748(s: seq<int>, i: nat)
  requires i <= |s|
  requires forall k :: 0 <= k < |s| ==> s[k] >= 0
  ensures Suf1748(s, i) >= 0
  decreases |s| - i
{ if i < |s| { SufNonNeg1748(s, i + 1); } }

// Codeforces 1256C: platform lengths are non-negative and fit in the n cells.
// (the statement says >= 1; 26 generated tests feed 0, so >= 0 is what is provable
// AND true of the data -- s >= -1 carries the extra case.)
method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
  requires a >= 0
  requires 0 <= b <= |d_list|
  requires c >= 1
  requires forall k :: 0 <= k < |d_list| ==> d_list[k] >= 0
  requires SumSeq(d_list) <= a
{
  SumFromIsSuf1748(d_list, 0, 0);
  var n := a;
  var m := b;
  var d := c;
  var ss := SumSeq(d_list);
  var ans := seq(n + 1, (idx: int) => 0);
  var s := 0;
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |ans| == n + 1
    invariant ss == Suf1748(d_list, i)
    invariant ss <= SumSeq(d_list)
    invariant s >= -1
    decreases m - i
  {
    SufNonNeg1748(d_list, i);
    SufNonNeg1748(d_list, i + 1);
    assert ss == d_list[i] + Suf1748(d_list, i + 1);
    var pos := if s + d <= n + 1 - ss then s + d else n + 1 - ss;
    assert 0 <= pos && pos + d_list[i] <= n + 1;
    var j := pos;
    while j < pos + d_list[i]
      invariant pos <= j <= pos + d_list[i]
      invariant |ans| == n + 1
      decreases pos + d_list[i] - j
    {
      ans := ans[j := i + 1];
      j := j + 1;
    }
    s := pos + d_list[i] - 1;
    ss := ss - d_list[i];
    i := i + 1;
  }
  if s + d <= n {
    output := "NO";
  } else {
    var parts: seq<string> := [];
    var k := 1;
    while k <= n
      invariant 1 <= k
      decreases n - k + 1
    {
      parts := parts + [IntToString(ans[k])];
      k := k + 1;
    }
    output := "YES\n" + Join(parts, " ");
  }
}
