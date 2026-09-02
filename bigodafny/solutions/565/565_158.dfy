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

  var maxV := 100000;
  var s := new int[maxV + 1];
  var z := 0;
  while z <= maxV
  {
    s[z] := 0;
    z := z + 1;
  }
  var i := 0;
  while i < |numbers|
  {
    s[numbers[i]] := s[numbers[i]] + 1;
    i := i + 1;
  }
  var found := false;
  var j := 0;
  while j <= maxV
  {
    if s[j] % 2 == 1 { found := true; }
    j := j + 1;
  }
  output := if found then "Conan" else "Agasa";
}
