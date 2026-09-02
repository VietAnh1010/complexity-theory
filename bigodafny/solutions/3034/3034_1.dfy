// 1150_C. Prefix Sum Primes  (problem 3034, solution 3034_1)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// 
// input = sys.stdin.readline
// 
// n = int(input())
// a = list(map(int, input().split()))
// 
// count = {1: 0, 2: 0}
// 
// for i in a:
//     count[i] += 1
// 
// if count[1] >= 1 and count[2] >= 1:
//     ans = [2] + [1] + [2]*(count[2]-1) + [1]*(count[1] - 1)
// elif count[1] == 0:
//     ans = [2] * count[2]
// elif count[2] == 0:
//     ans = [1] * count[1]
// 
// print(' '.join([str(x) for x in ans]))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var c1 := 0;
  var c2 := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    decreases |a_list| - i
  {
    if a_list[i] == 1 {
      c1 := c1 + 1;
    } else if a_list[i] == 2 {
      c2 := c2 + 1;
    }
    i := i + 1;
  }
  var ans: seq<int> := [];
  if c1 >= 1 && c2 >= 1 {
    ans := [2, 1];
    var k := 0;
    while k < c2 - 1
      invariant 0 <= k <= c2 - 1
      decreases (c2 - 1) - k
    {
      ans := ans + [2];
      k := k + 1;
    }
    k := 0;
    while k < c1 - 1
      invariant 0 <= k <= c1 - 1
      decreases (c1 - 1) - k
    {
      ans := ans + [1];
      k := k + 1;
    }
  } else if c1 == 0 {
    var k := 0;
    while k < c2
      invariant 0 <= k <= c2
      decreases c2 - k
    {
      ans := ans + [2];
      k := k + 1;
    }
  } else if c2 == 0 {
    var k := 0;
    while k < c1
      invariant 0 <= k <= c1
      decreases c1 - k
    {
      ans := ans + [1];
      k := k + 1;
    }
  }
  output := JoinInts(ans, " ");
}
