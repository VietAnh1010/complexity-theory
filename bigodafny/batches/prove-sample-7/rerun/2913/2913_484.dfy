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

include "../../../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires n >= 0
  ensures steps <= 4 * n + 6
{
  steps := 1;
  var a := 1;
  var found := false;
  var ans := 0;
  while a <= n && !found
    invariant 1 <= a <= n + 1
    invariant found ==> a <= n
    invariant !found ==> steps <= 4 * (a - 1) + 1
    invariant found ==> steps <= 4 * (a - 1) + 5
    decreases n - a, if found then 0 else 1
  {
    if a * a > n {
      ans := a;
      found := true;
      steps := steps + 1;
    } else {
      a := a + 1;
      steps := steps + 1;
    }
    steps := steps + 3;   // comparison a*a>n (1), loop guard re-evaluation (1), overhead (1)
  }
  if found {
    output := IntToString(ans) + " " + IntToString(ans) + "\n";
    steps := steps + 3;   // two IntToString (1 each) + concat (1)
  } else {
    output := "-1\n";
    steps := steps + 1;
  }
}
