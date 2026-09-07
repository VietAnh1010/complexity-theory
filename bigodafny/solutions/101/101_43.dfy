// 814_A. An abandoned sentiment from past  (problem 101, solution 101_43)
// time complexity: O(n+m)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
// N, K = map(int, input().split())
// a = list(map(int, input().split()))
// b = list(map(int, input().split()))
// if a.count(0) > 1: print("Yes")
// else:
//   for i in range(N):
//     if a[i] == 0:
//       a[i] = b[0]
//   for i in range(N - 1):
//     if a[i + 1] <= a[i]:
//       print("Yes")
//       break
//   else: print("No")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  var cnt := CountZeros(a_list);
  if cnt > 1 {
    output := "Yes\n";
  } else {
    var a := a_list;
    var bv := if |b_list| > 0 then b_list[0] else 0;
    var i := 0;
    while i < |a|
      invariant 0 <= i <= |a|
      decreases |a| - i
    {
      if a[i] == 0 {
        a := a[i := bv];
      }
      i := i + 1;
    }
    var found := false;
    var j := 0;
    while j < |a| - 1 && !found
      invariant 0 <= j <= |a|
      decreases |a| - j
    {
      if a[j+1] <= a[j] {
        found := true;
      }
      j := j + 1;
    }
    output := if found then "Yes\n" else "No\n";
  }
}

function CountZeros(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == 0 then 1 else 0) + CountZeros(s[1..])
}
