// 637_A. Voting for Photos  (problem 2947, solution 2947_115)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = input().split()
// b = set(a)
// maximum = -1
// maximum_id = []
// for i in b:
//     x = a.count(i)
//     if x > maximum:
//         maximum_id = [int(i)]
//         maximum = x
//     elif x == maximum:
//         maximum_id.append(int(i))
// a = a[::-1]
// maximum = -1
// answer = -1
// for i in maximum_id:
//     x = a.index(str(i))
//     if x > maximum:
//         answer = i
//         maximum = x
// print(answer)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var maxCount := -1;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    decreases |a_list| - i
  {
    var cnt := 0;
    var j := 0;
    while j < |a_list|
      invariant 0 <= j <= |a_list|
      decreases |a_list| - j
    {
      if a_list[j] == a_list[i] { cnt := cnt + 1; }
      j := j + 1;
    }
    if cnt > maxCount { maxCount := cnt; }
    i := i + 1;
  }

  var answer := -1;
  var bestLast := |a_list|;
  var seen: seq<int> := [];
  var k := 0;
  while k < |a_list|
    invariant 0 <= k <= |a_list|
    decreases |a_list| - k
  {
    var v := a_list[k];
    var alreadySeen := false;
    var sp := 0;
    while sp < |seen|
      invariant 0 <= sp <= |seen|
      decreases |seen| - sp
    {
      if seen[sp] == v { alreadySeen := true; }
      sp := sp + 1;
    }
    if !alreadySeen {
      seen := seen + [v];
      var cnt2 := 0;
      var p := 0;
      while p < |a_list|
        invariant 0 <= p <= |a_list|
        decreases |a_list| - p
      {
        if a_list[p] == v { cnt2 := cnt2 + 1; }
        p := p + 1;
      }
      if cnt2 == maxCount {
        var lastIdx := -1;
        var q := 0;
        while q < |a_list|
          invariant 0 <= q <= |a_list|
          decreases |a_list| - q
        {
          if a_list[q] == v { lastIdx := q; }
          q := q + 1;
        }
        if lastIdx < bestLast {
          bestLast := lastIdx;
          answer := v;
        }
      }
    }
    k := k + 1;
  }
  output := IntToString(answer);
}
