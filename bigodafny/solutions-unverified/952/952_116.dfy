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

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
{
  var dc: map<int, int> := map[];
  var order: seq<int> := [];
  var idx := 0;
  while idx < |a_list|
    invariant 0 <= idx <= |a_list|
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
  }
  var ans := 0;
  var mx := 0;
  var k := 0;
  while k < |order|
    invariant 0 <= k <= |order|
    invariant forall v :: v in order ==> v in dc
    decreases |order| - k
  {
    var xx := order[k];
    if dc[xx] > mx {
      mx := dc[xx];
      ans := xx;
    }
    k := k + 1;
  }
  var arr: seq<int> := [];
  var i := n - 1;
  while i >= 0
    invariant -1 <= i <= n - 1
    decreases i + 1
  {
    if a_list[i] == ans {
      ans := ans - 1;
      arr := arr + [i + 1];
    }
    i := i - 1;
  }
  output := IntToString(|arr|) + "\n" + JoinInts(ReverseInts(arr), " ") + "\n";
}

function ReverseInts(s: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then [] else ReverseInts(s[1..]) + [s[0]]
}
