// 346_A. Alice and Bob  (problem 1386, solution 1386_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// n = int(input())
// arr = list(map(int, input().split()))
// 
// gcd = 0
// for num in arr:
// 	gcd = math.gcd(gcd, num)
// 
// moves = max(arr) / gcd - n
// if moves % 2:
// 	print('Alice')
// else:
// 	print('Bob')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
