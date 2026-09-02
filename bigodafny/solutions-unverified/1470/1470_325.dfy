// 999_A. Mishka and Contest  (problem 1470, solution 1470_325)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a,b = map(int,input().split())
// l= [int(i) for i in input().split()]
// 
// c=0
// while len(l)>0:
//     premier = l[0]
//     last= l[-1]
//     if premier<=b:
//         c+=1
//         del l[0]
//     elif last<=b:
//         c+=1
//         del l[-1]
//     else:
//         break
// 
// print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  var lo := 0;
  var hi := n - 1;
  var c := 0;
  var stop := false;
  while lo <= hi && !stop
    decreases hi - lo + 1
  {
    if a_list[lo] <= k {
      c := c + 1;
      lo := lo + 1;
    } else if a_list[hi] <= k {
      c := c + 1;
      hi := hi - 1;
    } else {
      stop := true;
    }
  }
  output := IntToString(c);
}
