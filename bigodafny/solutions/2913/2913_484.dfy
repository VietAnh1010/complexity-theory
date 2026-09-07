// 1088_A. Ehab and another construction problem  (problem 2913, solution 2913_484)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def Calculo_Brute_Force(x):
//     
//     for a in range(1,x+1):
//             if ((a*a)>x) :
//                 print (a,a)
//                 return(a,a)
//     
//     print(-1)
//     return(-1)
// 
// Calculo_Brute_Force(int(input()))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var a := 1;
  var found := false;
  var ans := 0;
  while a <= n && !found
    invariant 1 <= a
    decreases n - a, if found then 0 else 1
  {
    if a * a > n {
      ans := a;
      found := true;
    } else {
      a := a + 1;
    }
  }
  if found {
    output := IntToString(ans) + " " + IntToString(ans) + "\n";
  } else {
    output := "-1\n";
  }
}
