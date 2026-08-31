// 208_D. Prizes, Prizes, more Prizes  (problem 1092, solution 1092_11)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// sum,a,b,c,d,e=0,0,0,0,0,0
// numbers = [int(x) for x in input().split(' ')]
// prizes = [int(x) for x in input().split(' ')]
// prizes.sort()
// 
// for num in numbers:
//     sum+=num
//     if sum >= prizes[4]:
//         e+=int(sum/prizes[4])
//         sum = sum%prizes[4]
//     if sum >= prizes[3]:
//         d+=int(sum/prizes[3])
//         sum = sum%prizes[3]
//     if sum >= prizes[2]:
//         c+=int(sum/prizes[2])
//         sum = sum%prizes[2]
//     if sum >= prizes[1]:
//         b+=int(sum/prizes[1])
//         sum = sum%prizes[1]
//     if sum >= prizes[0]:
//         a+=int(sum/prizes[0])
//         sum = sum%prizes[0]
// print(f'{a} {b} {c} {d} {e}')
// print(sum)
//   		 	    		 	 	  	   					 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  var prizes := SortInts(b_list);
  var aC := 0;
  var bC := 0;
  var cC := 0;
  var dC := 0;
  var eC := 0;
  var s := 0;
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    s := s + a_list[idx];
    if s >= prizes[4] { eC := eC + FloorDiv(s, prizes[4]); s := FloorMod(s, prizes[4]); }
    if s >= prizes[3] { dC := dC + FloorDiv(s, prizes[3]); s := FloorMod(s, prizes[3]); }
    if s >= prizes[2] { cC := cC + FloorDiv(s, prizes[2]); s := FloorMod(s, prizes[2]); }
    if s >= prizes[1] { bC := bC + FloorDiv(s, prizes[1]); s := FloorMod(s, prizes[1]); }
    if s >= prizes[0] { aC := aC + FloorDiv(s, prizes[0]); s := FloorMod(s, prizes[0]); }
    idx := idx + 1;
  }
  output := Join([IntToString(aC), IntToString(bC), IntToString(cC), IntToString(dC), IntToString(eC)], " ") + "\n" + IntToString(s);
}

