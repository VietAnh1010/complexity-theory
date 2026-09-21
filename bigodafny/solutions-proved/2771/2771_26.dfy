// 56_B. Spoilt Permutation  (problem 2771, solution 2771_26)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = [0]+list(map(int, input().split()))
// l, r = -1, -1
// i = 0
// while(i<n and arr[i]+1==arr[i+1]):
//     i+=1
// l = i
// i+=1
// while(i<n and arr[i]-1==arr[i+1]):
//     i+=1
//     r = i
// i+=1
// while(i<n and arr[i]+1==arr[i+1]):
//     i+=1
// if(r != -1 and i>= n-1):
//     print(l+1, r)
// else:
//     print(0, 0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| == n + 1
  requires n >= 0
  ensures steps <= 15 * n + 20
{
  steps := 1;
  var arr := a_list;
  var l := -1;
  var r := -1;
  var i := 0;
  while i < n && arr[i] + 1 == arr[i + 1]
    invariant 0 <= i <= n
    invariant steps <= 1 + 4 * i
    decreases n - i
  {
    i := i + 1;
    steps := steps + 4;
  }
  l := i;
  i := i + 1;
  steps := steps + 2;
  ghost var base2 := steps;
  var i0 := i;
  while i < n && arr[i] - 1 == arr[i + 1]
    invariant i0 <= i
    invariant i == i0 || i <= n
    invariant steps <= base2 + 4 * (i - i0)
    decreases n - i
  {
    i := i + 1;
    r := i;
    steps := steps + 4;
  }
  i := i + 1;
  steps := steps + 2;
  ghost var base3 := steps;
  var i1 := i;
  while i < n && arr[i] + 1 == arr[i + 1]
    invariant i1 <= i
    invariant i == i1 || i <= n
    invariant steps <= base3 + 4 * (i - i1)
    decreases n - i
  {
    i := i + 1;
    steps := steps + 4;
  }
  if r != -1 && i >= n - 1 {
    output := IntToString(l + 1) + " " + IntToString(r) + "\n";
    steps := steps + 4;
  } else {
    output := "0 0\n";
    steps := steps + 1;
  }
}
