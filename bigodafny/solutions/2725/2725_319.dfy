// 999_C. Alphabetic Removals  (problem 2725, solution 2725_319)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=list(map(int,input().split()))
// s=list(input())
// x=sorted([j,i] for i,j in enumerate(s))
// #print(x)
// for i in range(k):
//     s[x[i][1]]=''
// print(''.join(s))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, s: string) returns (output: string)
{
  var pairArr := new (char, int)[|s|];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
  {
    pairArr[i] := (s[i], i);
    i := i + 1;
  }
  var pairs := pairArr[..];
  var sorted := Sort(pairs, (x: (char, int), y: (char, int)) => x.0 < y.0 || (x.0 == y.0 && x.1 < y.1));
  var removed := new bool[|s|];
  var z := 0;
  while z < |s|
    invariant 0 <= z <= |s|
  {
    removed[z] := false;
    z := z + 1;
  }
  var j := 0;
  while j < k && j < |sorted|
    invariant 0 <= j <= |sorted|
  {
    var target := sorted[j].1;
    if 0 <= target < |s| {
      removed[target] := true;
    }
    j := j + 1;
  }
  var buf := new char[|s|];
  var w := 0;
  var m := 0;
  while m < |s|
    invariant 0 <= m <= |s|
    invariant 0 <= w <= m
  {
    if !removed[m] {
      buf[w] := s[m];
      w := w + 1;
    }
    m := m + 1;
  }
  output := buf[0..w];
}
