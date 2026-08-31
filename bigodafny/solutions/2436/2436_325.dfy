// 1111_A. Superhero Transformation  (problem 2436, solution 2436_325)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// cons=['b', 'c', 'd','f', 'g', 'h', 'j', 'k', 'l', 'm', 'n', 'p', 'q', 'r', 's', 't','v', 'w', 'x', 'y', 'z']
// vow=['a','e','i','o','u']
// a=input()
// b=input()
// n=len(a)
// a=list(a)
// b=list(b)
// i=0
// while(i<n): 
//     if (n!=len(b)):
//         print('No')
//         break
//     if ((a[i] in cons) and (b[i] in vow)) or ((a[i] in vow) and (b[i] in cons)):
//         print("No")
//         break
//     i=i+1
// if (i==n):
//     print("Yes")
// 
//                     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: string, b: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
