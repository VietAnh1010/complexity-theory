// 192_A. Funky Numbers  (problem 2065, solution 2065_128)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #codeforces.com:3.2.5(2.4.0)
// import math
// a=int(input())*2;b=0
// for i in range(1,int(math.sqrt(a))):
//     c=a-i*i-i;d=int(math.sqrt(c))
//     if d*(d+1)==c:b=1
// print("YES")if(b)else print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
