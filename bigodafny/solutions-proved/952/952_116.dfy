// 977_F. Consecutive Subsequence  (problem 952, solution 952_116)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// dc = dict()
// for x in a:
//     dc[x] = max(dc.get(x, 0), dc.get(x - 1, 0) + 1)
// ans = 0
// mx = 0
// for x in dc.keys():
//     if dc[x] > mx:
//         mx = dc[x]
//         ans = x
// arr = []
// for i in range(n - 1, -1, -1):
//     if a[i] == ans:
//         ans -= 1
//         arr.append(i + 1)
// print(len(arr))
// print(*arr[::-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  ensures steps <= 40 * |a_list| + 30 + 3 * |output|
{
  steps := 1;
  var dc: map<int, int> := map[];
  var order: seq<int> := [];
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
    invariant |order| <= idx
    invariant steps <= 1 + 14 * idx
    invariant forall v :: v in order ==> v in dc
    decreases |a_list| - idx
  {
    var x := a_list[idx];
    var cur := if x in dc then dc[x] else 0;
    var prevChain := if (x - 1) in dc then dc[x - 1] else 0;
    var newval := if cur > prevChain + 1 then cur else prevChain + 1;
    if !(x in dc) {
      order := order + [x];
    }
    dc := dc[x := newval];
    idx := idx + 1;
    steps := steps + 14;
  }
  var ans := 0;
  var mx := 0;
  var k := 0;
  while k < |order|
    invariant 0 <= k <= |order|
    invariant |order| <= |a_list|
    invariant steps <= 1 + 14 * |a_list| + 8 * k
    invariant forall v :: v in order ==> v in dc
    decreases |order| - k
  {
    var xx := order[k];
    if dc[xx] > mx {
      mx := dc[xx];
      ans := xx;
    }
    k := k + 1;
    steps := steps + 8;
  }
  var arr: seq<int> := [];
  var i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    invariant |arr| <= n - 1 - i
    invariant steps <= 1 + 22 * |a_list| + 8 * (n - 1 - i)
    decreases i + 1
  {
    if a_list[i] == ans {
      ans := ans - 1;
      arr := arr + [i + 1];
    }
    i := i - 1;
    steps := steps + 8;
  }
  ghost var rv := ReverseInts(arr);
  ReverseLen(arr);
  SumDigitsReverse(arr);
  output := IntToString(|arr|) + "\n" + JoinInts(ReverseInts(arr), " ") + "\n";
  IntToStringDigits(|arr|);
  if |arr| > 0 { JoinIntsLen(rv, " "); }
  steps := steps + 3 * |arr| + 1 + Digits(|arr|) + 2 + SumDigits(rv) + |rv| + 2;
}

function ReverseInts(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [] else ReverseInts(s[1..]) + [s[0]]
}

lemma ReverseLen(s: seq<int>)
  ensures |ReverseInts(s)| == |s|
  decreases |s|
{
  if |s| > 0 { ReverseLen(s[1..]); }
}

lemma SumDigitsReverse(s: seq<int>)
  ensures SumDigits(ReverseInts(s)) == SumDigits(s)
  decreases |s|
{
  if |s| > 0 {
    SumDigitsReverse(s[1..]);
    SumDigitsSnoc(ReverseInts(s[1..]), s[0]);
    assert SumDigits(s) == Digits(s[0]) + SumDigits(s[1..]);
  }
}

lemma SumDigitsSnoc(s: seq<int>, x: int)
  ensures SumDigits(s + [x]) == SumDigits(s) + Digits(x)
  decreases |s|
{
  if |s| > 0 {
    assert (s + [x])[1..] == s[1..] + [x];
    SumDigitsSnoc(s[1..], x);
  }
}
