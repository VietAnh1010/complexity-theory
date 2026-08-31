// 703_A. Mishka and Game  (problem 408, solution 408_2)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// m=0
// c=0
// a=[]
// for i in range(n):
// 	a.append(list(map(int,input().split())))	
// 	if a[i][0]>a[i][1]:
// 		m+=1
// 	if a[i][1]>a[i][0]:
// 		c+=1
// if m>c:
// 	print("Mishka")
// if m<c:
// 	print("Chris")			
// if m==c:
// 	print("Friendship is magic!^^")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var m := 0;
  var c := 0;
  var i := 0;
  while i < |pairs_list|
    decreases |pairs_list| - i
  {
    var a := pairs_list[i][0];
    var b := pairs_list[i][1];
    if a > b { m := m + 1; }
    if b > a { c := c + 1; }
    i := i + 1;
  }
  if m > c {
    output := "Mishka";
  } else if m < c {
    output := "Chris";
  } else {
    output := "Friendship is magic!^^";
  }
}
