// 52_A. 123-sequence  (problem 2193, solution 2193_70)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l = list(map(int,input().split()))
// freq = {} 
// for item in l: 
//     if (item in freq): 
//         freq[item] += 1
//     else: 
//         freq[item] = 1
// l = list(sorted(freq.values(),reverse=True))
// l.remove(l[0])
// print(sum(l)) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| >= 1
{
  var distinct: seq<int> := [];
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant i >= 1 ==> |distinct| >= 1
    decreases |a_list| - i
  {
    var v := a_list[i];
    if v !in distinct { distinct := distinct + [v]; }
    i := i + 1;
  }
  assert |distinct| >= 1;
  var counts: seq<int> := [];
  var j := 0;
  while j < |distinct|
    invariant 0 <= j <= |distinct|
    invariant |counts| == j
    decreases |distinct| - j
  {
    var v := distinct[j];
    var c := 0;
    var k := 0;
    while k < |a_list|
      invariant 0 <= k <= |a_list|
      decreases |a_list| - k
    {
      if a_list[k] == v { c := c + 1; }
      k := k + 1;
    }
    counts := counts + [c];
    j := j + 1;
  }
  assert |counts| >= 1;
  var sortedCounts := Sort(counts, (x: int, y: int) => x > y);
  assert |sortedCounts| >= 1;
  var total := SumSeq(sortedCounts[1..]);
  output := IntToString(total);
}
