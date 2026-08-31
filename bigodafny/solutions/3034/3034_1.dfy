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
  output := ""; // TODO: translate the Python above
}
