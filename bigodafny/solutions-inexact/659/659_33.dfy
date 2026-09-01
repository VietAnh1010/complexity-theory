// 127_B. Canvas Frames  (problem 659, solution 659_33)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// m=list(map(int,input().split()))
// k=set(m)
// k=list(k)
// c=0
// for i in k:
// 	c+=m.count(i)//2
// print(c//2)	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, ratings: seq<int>) returns (output: string)
{
  var distinct: seq<int> := [];
  var i := 0;
  while i < |ratings|
    decreases |ratings| - i
  {
    if ratings[i] !in distinct {
      distinct := distinct + [ratings[i]];
    }
    i := i + 1;
  }
  var c := 0;
  i := 0;
  while i < |distinct|
    decreases |distinct| - i
  {
    var cnt := CountOccurrences659(ratings, distinct[i]);
    c := c + cnt / 2;
    i := i + 1;
  }
  output := IntToString(c / 2);
}

method CountOccurrences659(xs: seq<int>, v: int) returns (cnt: int)
{
  cnt := 0;
  var i := 0;
  while i < |xs|
    decreases |xs| - i
  {
    if xs[i] == v { cnt := cnt + 1; }
    i := i + 1;
  }
}
