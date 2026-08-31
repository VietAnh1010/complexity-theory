// 546_C. Soldier and Cards  (problem 2680, solution 2680_221)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [int(x) for x in input().split()]
// a = a[1:]
// b = [int(x) for x in input().split()]
// b = b[1:]
// k = 0
// while len(a) > 0 and len(b) > 0 and k <= 10 ** 3:
// 	if a[0] > b[0] and (not(a[0] == 0 and b[0] == 9) and not(a[0] == 9 and b[0] == 0)):
// 		a.append(b[0])
// 		a.append(a[0])
// 		a.pop(0)
// 		b.pop(0)
// 		k += 1
// 	else:
// 		b.append(a[0])
// 		b.append(b[0])
// 		a.pop(0)
// 		b.pop(0)
// 		k += 1
// if len(a) != 0 and len(b) != 0:
// 	print(-1)
// elif len(a) > 0:
// 	print(k, 1)
// else:
// 	print(k, 2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, list1: seq<int>, list2: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
