// 914_B. Conan and Agasa play a Card Game  (problem 565, solution 565_158)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// arr=list(map(int,input().split()))
// arrx=[]
// arr.sort(reverse=True)
// i=0
// while(i<n):
// 	count=0
// 	val=arr[i]
// 	while(i<n and arr[i]==val):
// 		i+=1
// 		count+=1
// 	arrx.append(count)
// flag=0
// for i in range(len(arrx)):
// 	if(arrx[i]%2!=0):
// 		flag=1
// 		break
// if(flag==0):
// 	print('Agasa')
// else:
// 	print('Conan')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
