// 8_B. Obsession with Robots  (problem 949, solution 949_38)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// x,y=0,0
// used=set()
// used.add((x,y))
// bo=0
// for e in s:
//     if(e=='L'):
//         x+=1
//     elif(e=='R'):
//         x-=1
//     elif(e=='U'):
//         y+=1
//     else:
//         y-=1
//     a=(x-1,y) in used
//     b=(x+1,y) in used
//     c=(x,y-1) in used
//     d=(x,y+1) in used
//     if(a+b+c+d>1):
//         bo=1
//     if((x,y) in used):
//         bo=1
//     used.add((x,y))
// print("OK" if not bo else "BUG")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(directions: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
