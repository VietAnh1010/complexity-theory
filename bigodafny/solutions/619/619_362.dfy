// 975_A. Aramic script  (problem 619, solution 619_362)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=str(input()) 
// arr = [str(x) for x in input().split()]
// 
// 
// ss = set()
// 
// for x in arr:
//       a2 = []
//       s=""
//       for i in range(int(26)):
//               a2.append(0)
//       for i in range(len(x)):
//               nu = ord(x[i]) 
//               nu = nu - ord('a')
//               a2[nu]=1 
//       for i in range(int(26)): 
//             if a2[i]==1:
//                 s=s+str(chr(i +ord('a'))) 
//       ss.add(s) 
// 
// 
// print(len(ss))
//       
//        
//      
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
