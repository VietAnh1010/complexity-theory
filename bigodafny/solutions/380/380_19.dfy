// 525_B. Pasha and String  (problem 380, solution 380_19)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s = list(input())
// n = len(s)
// m = int(input())
// a = list(map(int,input().split()))
// l = [0]*(n+1)
// for i in a:
// 	l[i-1]+=1
// 	l[n-i+1]-=1
// k = 0
// l2 = []
// for i in range(n):
// 	k += l[i]
// 	if k%2==0:
// 		l2.append(s[i])
// 	else:
// 		l2.append(s[n-i-1])
// print("".join(l2)) 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string, n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
