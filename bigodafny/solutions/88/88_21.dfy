// 1202_A. You Are Given Two Binary Strings...  (problem 88, solution 88_21)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for i in range(n):
// 	a=input()
// 	b=input()
// 	k=b[::-1].index("1")
// 	a=a[::-1]
// 	p=a[k::].index("1")
// 	print(p)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_list: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
