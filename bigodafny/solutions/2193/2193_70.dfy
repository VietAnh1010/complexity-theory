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
{
  var distinct: seq<int> := [];
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var v := a_list[i];
    if v !in distinct { distinct := distinct + [v]; }
    i := i + 1;
  }
  var counts: seq<int> := [];
  var j := 0;
  while j < |distinct|
    decreases |distinct| - j
  {
    var v := distinct[j];
    var c := 0;
    var k := 0;
    while k < |a_list|
      decreases |a_list| - k
    {
      if a_list[k] == v { c := c + 1; }
      k := k + 1;
    }
    counts := counts + [c];
    j := j + 1;
  }
  var sortedCounts := Sort(counts, (x: int, y: int) => x > y);
  var total := SumSeq(sortedCounts[1..]);
  output := IntToString(total);
}
