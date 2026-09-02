// 605_A. Sorting Railway Cars  (problem 1053, solution 1053_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// arr=list(map(int,input().split()))
// l=[n]*(n+1)
// for c in arr:
//  l[c]=l[c-1]-1
// print(min(l))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, a_list: seq<int>) returns (output: string)
{
  var l := new int[N + 1];
  var ii := 0;
  while ii <= N
    decreases N - ii
  {
    l[ii] := N;
    ii := ii + 1;
  }
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    var c := a_list[idx];
    l[c] := l[c - 1] - 1;
    idx := idx + 1;
  }
  var minVal := l[0];
  var kk := 1;
  while kk <= N
    decreases N - kk
  {
    if l[kk] < minVal { minVal := l[kk]; }
    kk := kk + 1;
  }
  output := IntToString(minVal);
}

