// 999_A. Mishka and Contest  (problem 1470, solution 1470_470)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// arr=list(map(int, input().split(' ')))
// ar=list(map(int, input().split(' ')))
// t=0
// for i in range (arr[0]):
//     if ar[i]>arr[1]:
//         t=ar.index(ar[i])
//         break
// ar.reverse()
// z=0
// for each in ar:
//     if each>arr[1]:
//         z=ar.index(each)
//         break
// ar=sorted(ar)
// s=0
// for h in ar:
//     if h>arr[1]:
//         s=1
// if s==0:
//     print (arr[0])
// else:
//     print (z+t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| == n
  ensures steps <= 2 * NLogN(n) + 30 * n + 30 + |output|
{
  steps := 0;
  var ar := a_list;
  var t := 0;
  var i := 0;
  ghost var brk := false;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 4 * i + (if brk then 3 * n + 6 else 0)
    decreases n - i
  {
    steps := steps + 4;
    if ar[i] > k {
      var cost;
      t, cost := Index1470(ar, ar[i]);
      steps := steps + cost;
      brk := true;
      break;
    }
    i := i + 1;
  }
  assert steps <= 4 * n + 3 * n + 6;
  var rev: seq<int> := [];
  var r := |ar|;
  ghost var s1 := steps;
  while r > 0
    invariant 0 <= r <= |ar|
    invariant |rev| == |ar| - r
    invariant steps == s1 + 6 * (|ar| - r)
    decreases r
  {
    rev := rev + [ar[r - 1]];
    r := r - 1;
    steps := steps + 6;
  }
  ar := rev;
  var z := 0;
  i := 0;
  brk := false;
  ghost var s2 := steps;
  while i < |ar|
    invariant 0 <= i <= |ar|
    invariant |ar| == n
    invariant steps <= s2 + 4 * i + (if brk then 3 * n + 6 else 0)
    decreases |ar| - i
  {
    steps := steps + 4;
    if ar[i] > k {
      var cost;
      z, cost := Index1470(ar, ar[i]);
      steps := steps + cost;
      brk := true;
      break;
    }
    i := i + 1;
  }
  assert steps <= s2 + 4 * n + 3 * n + 6;
  ar := SortInts(ar);
  steps := steps + SortCost(n);
  SortCostWithin(n, n);
  var s := 0;
  i := 0;
  ghost var s3 := steps;
  while i < |ar|
    invariant 0 <= i <= |ar|
    invariant steps == s3 + 4 * i
    decreases |ar| - i
  {
    if ar[i] > k { s := 1; }
    i := i + 1;
    steps := steps + 4;
  }
  if s == 0 {
    output := IntToString(n);
    IntToStringDigits(n);
    steps := steps + Digits(n);
  } else {
    output := IntToString(z + t);
    IntToStringDigits(z + t);
    steps := steps + Digits(z + t);
  }
}

// list.index: position of the first occurrence of x
method Index1470(xs: seq<int>, x: int) returns (idx: int, ghost steps: nat)
  requires x in xs
  ensures 0 <= idx < |xs|
  ensures steps <= 3 * |xs| + 2
{
  steps := 1;
  idx := 0;
  while xs[idx] != x
    invariant 0 <= idx < |xs|
    invariant x !in xs[..idx]
    invariant steps == 1 + 3 * idx
    decreases |xs| - idx
  {
    assert xs[..idx + 1] == xs[..idx] + [xs[idx]];
    idx := idx + 1;
    steps := steps + 3;
  }
  steps := steps + 1;
}
