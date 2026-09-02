// 397_A. On Segment's Own Points  (problem 2607, solution 2607_25)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// from re import findall
// 
// n = int(input())
// y = [int(i) for i in input().split()]
// alex = list(range(y[1]))
// for i in range(n-1):
//     a, b  = [int(x) for x in input().split()]
//     for j in range(a, min(b, y[1])):
//         alex[j] = 'X'
// 
// o = [str(x) for x in (alex[y[0]:y[1]])]
// o = filter(lambda el: el is not 'X', o)
// 
// print(len(list(o)))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>) returns (output: string)
  requires n == |intervals|
  requires forall k :: 0 <= k < |intervals| ==> |intervals[k]| >= 2
  requires n >= 1
{
  var y0 := intervals[0][0];
  var y1 := intervals[0][1];
  var sz := if y1 > 0 then y1 else 0;
  var marked := seq(sz, _ => false);
  var k := 1;
  while k < n
    invariant 1 <= k <= n
    invariant |marked| == sz
    decreases n - k
  {
    var a := intervals[k][0];
    var b := intervals[k][1];
    var hi := if b < y1 then b else y1;
    var j := a;
    while j < hi
      invariant |marked| == sz
      decreases hi - j
    {
      if 0 <= j < sz {
        marked := marked[j := true];
      }
      j := j + 1;
    }
    k := k + 1;
  }
  var cnt := 0;
  var t := y0;
  while t < y1
    invariant |marked| == sz
    decreases y1 - t
  {
    if 0 <= t < sz && !marked[t] {
      cnt := cnt + 1;
    }
    t := t + 1;
  }
  output := IntToString(cnt);
}
