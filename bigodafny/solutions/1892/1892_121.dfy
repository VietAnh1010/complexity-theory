// 1149_A. Prefix Sum Primes  (problem 1892, solution 1892_121)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// l=list(map(int,input().split()))
// flag1=0
// flag2=0
// for i in range(n):
// 	if l[i]==2:
// 		flag1=1
// 		break
// for i in range(n):
// 	if l[i]==1:
// 		flag2=1
// 		break
// if flag1==0 or flag2==0:
// 	print(*l)
// else:
// 	print(2,1,end=' ')
// 	l.remove(2)
// 	l.remove(1)
// 	l.sort(reverse=True)
// 	print(*l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
