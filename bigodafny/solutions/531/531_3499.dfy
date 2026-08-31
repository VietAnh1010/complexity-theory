// 263_A. Beautiful Matrix  (problem 531, solution 531_3499)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # n=int(input())
// # x=list(map(int,input().split()))
// # x.sort()
// # print(x)
// 
// # fi=fj=0
// # for i in range(5):
// # 		x=input().split()
// # 		k=0
// # 		for j in x:
// # 			if j=="1":
// # 				fi=i
// # 				fj=k
// # 			k+=1
// 
// # t1,t2=abs(fi-2),abs(fj-2)
// # print(t1+t2)
// 
// 
// 
// for i in range(5):
// 	try:
// 		print(abs(2-i) + abs(2-input().split().index("1")))
// 	except:
// 		pass
// 
// 
// 		
// 
// 
// 	
// 
// 
// 
// 
// 
// 
// 
// 
// 
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(matrix: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
