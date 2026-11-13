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

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == n
{
  var ar := a_list;
  var t := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    if ar[i] > k {
      t := Index1470(ar, ar[i]);
      break;
    }
    i := i + 1;
  }
  // ar.reverse()
  var rev: seq<int> := [];
  var r := |ar|;
  while r > 0
    invariant 0 <= r <= |ar|
    invariant |rev| == |ar| - r
    decreases r
  {
    rev := rev + [ar[r - 1]];
    r := r - 1;
  }
  ar := rev;
  var z := 0;
  i := 0;
  while i < |ar|
    invariant 0 <= i <= |ar|
    decreases |ar| - i
  {
    if ar[i] > k {
      z := Index1470(ar, ar[i]);
      break;
    }
    i := i + 1;
  }
  ar := SortInts(ar);
  var s := 0;
  i := 0;
  while i < |ar|
    invariant 0 <= i <= |ar|
    decreases |ar| - i
  {
    if ar[i] > k { s := 1; }
    i := i + 1;
  }
  if s == 0 {
    output := IntToString(n);
  } else {
    output := IntToString(z + t);
  }
}

// list.index: position of the first occurrence of x
method Index1470(xs: seq<int>, x: int) returns (idx: int)
  requires x in xs
  ensures 0 <= idx < |xs|
{
  idx := 0;
  while xs[idx] != x
    invariant 0 <= idx < |xs|
    invariant x !in xs[..idx]
    decreases |xs| - idx
  {
    assert xs[..idx + 1] == xs[..idx] + [xs[idx]];
    idx := idx + 1;
  }
}
