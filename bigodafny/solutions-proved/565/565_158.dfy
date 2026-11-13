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

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires forall k :: 0 <= k < |numbers| ==> 1 <= numbers[k] <= 100000
  ensures steps <= 2 * NLogN(|numbers|) + 16 * |numbers| + 8
{
  steps := SortCost(|numbers|);
  SortCostWithin(|numbers|, |numbers|);
  var arr := Sort(numbers, (x: int, y: int) => x > y);
  var m := |arr|;
  steps := steps + 2;
  var arrx: seq<int> := [];
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |arrx| <= i
    invariant steps <= SortCost(|numbers|) + 2 + 11 * i
    decreases m - i
  {
    ghost var s0 := steps;
    var count := 0;
    var val := arr[i];
    var i0 := i;
    while i < m && arr[i] == val
      invariant i0 <= i <= m
      invariant i == i0 ==> (i < m && arr[i] == val)
      invariant steps <= s0 + 5 * (i - i0)
      decreases m - i
    {
      i := i + 1;
      count := count + 1;
      steps := steps + 5;
    }
    arrx := arrx + [count];
    steps := steps + 6;
  }
  var flag := 0;
  var k := 0;
  while k < |arrx|
    invariant 0 <= k <= |arrx|
    invariant steps <= SortCost(|numbers|) + 2 + 11 * m + 5 * k
    decreases |arrx| - k
  {
    steps := steps + 5;
    if arrx[k] % 2 != 0 {
      flag := 1;
      break;
    }
    k := k + 1;
  }
  if flag == 0 {
    output := "Agasa";
    steps := steps + 1;
  } else {
    output := "Conan";
    steps := steps + 1;
  }
}
