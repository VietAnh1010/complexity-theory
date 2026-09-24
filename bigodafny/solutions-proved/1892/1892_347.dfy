// 1149_A. Prefix Sum Primes  (problem 1892, solution 1892_347)
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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires 0 <= n <= |a_list|
  ensures steps <= 10 * n + 20
{
  steps := 1;
  var count1 := 0;
  var count2 := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant count1 + count2 <= i
    invariant steps <= 1 + 4 * i
    decreases n - i
  {
    steps := steps + 1;
    if a_list[i] == 1 {
      count1 := count1 + 1;
      steps := steps + 1;
    } else if a_list[i] == 2 {
      count2 := count2 + 1;
      steps := steps + 1;
    }
    i := i + 1;
    steps := steps + 2;
  }
  var ans: seq<int>;
  if count1 >= 1 && count2 >= 1 {
    ans := [2] + [1] + seq(count2 - 1, _ => 2) + seq(count1 - 1, _ => 1);
    steps := steps + 2 + (count2 - 1) + (count1 - 1);
  } else if count1 == 0 {
    ans := seq(count2, _ => 2);
    steps := steps + count2;
  } else {
    ans := seq(count1, _ => 1);
    steps := steps + count1;
  }
  assert |ans| <= n;
  output := JoinInts(ans, " ");
  steps := steps + 3 * |ans| + 1;
}
