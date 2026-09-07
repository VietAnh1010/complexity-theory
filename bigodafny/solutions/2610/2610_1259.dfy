// 490_A. Team Olympiad  (problem 2610, solution 2610_1259)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input());t = 0;t2 = 0
// l = [int(i) for i in input().split()]
// l2 = l[:]
// l2.sort()
// #print('l2',l2)
// t1 = l.count(1)
// t2 = l.count(2)
// t3 = l.count(3)
// i1 = 0
// i2 = t1
// i3 = t1+t2
// print(min(t1,t2,t3))
// for i in range(min(t1,t2,t3)):
// #print('l2',l2)
// #	print(i1,i2,i3)
// 	print(l.index(l2[i1])+1,l.index(l2[i2])+1,l.index(l2[i3])+1)
// 	l[l.index(l2[i1])] = -1
// 	l[l.index(l2[i2])] = -1
// 	l[l.index(l2[i3])] = -1
// 	l2[i1] = -1;l2[i2] = -2;l2[i3] = -3
// 	
// 	
// 	i1+=1;i2+=1;i3+=1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
