// 1244_A. Pens and Pencils  (problem 89, solution 89_463)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// for i in range(n):
//    k=list(map(int,input().split()))
//    if k[0]%k[2]==0:
//      x=k[0]//k[2]
//    else:
//      x=k[0]//k[2]+1
//    if k[1]%k[3]==0:
//      y=k[1]//k[3]
//    else:
//      y=k[1]//k[3]+1
//    if (x+y)<=k[-1]:
//      print(x,y)
//    else:
//      print('-1')
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

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var k := lists[i];
    assume {:axiom} |k| >= 5;
    var k0 := k[0];
    var k1 := k[1];
    var k2 := k[2];
    var k3 := k[3];
    var k4 := k[4];
    var x := if k0 % k2 == 0 then k0 / k2 else k0 / k2 + 1;
    var y := if k1 % k3 == 0 then k1 / k3 else k1 / k3 + 1;
    if x + y <= k4 {
      parts := parts + [IntToString(x) + " " + IntToString(y)];
    } else {
      parts := parts + ["-1"];
    }
    i := i + 1;
  }
  output := Join(parts, "\n");
}
