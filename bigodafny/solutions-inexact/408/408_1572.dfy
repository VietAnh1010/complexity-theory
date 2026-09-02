// 703_A. Mishka and Game  (problem 408, solution 408_1572)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// h=k=0
// for i in range(n):
//     a,b=map(int,input().split())
//     if(a>b):
//         h+=1
//     elif(a<b):
//         k+=1
// if(h>k):
//     print("Mishka")
// elif(h==k):
//     print("Friendship is magic!^^")
// else:
//     print("Chris")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var h := 0;
  var k := 0;
  var i := 0;
  while i < |pairs_list|
    decreases |pairs_list| - i
  {
    var a := pairs_list[i][0];
    var b := pairs_list[i][1];
    if a > b { h := h + 1; } else if a < b { k := k + 1; }
    i := i + 1;
  }
  if h > k {
    output := "Mishka";
  } else if h == k {
    output := "Friendship is magic!^^";
  } else {
    output := "Chris";
  }
}
