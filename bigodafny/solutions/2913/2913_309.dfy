// 1088_A. Ehab and another construction problem  (problem 2913, solution 2913_309)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t = int(input())
// flag=0
// for i in range(1,t+1):
//     if flag!=1:
//         for j in range(1,t+1):
//             if flag!=1:
//                 if i%j == 0:
//                     if i*j>t:
//                         if i%j < t:
//                             a,b = i,j
//                             flag=1
// if flag==1:
//     print(a,b)
// else:
//     print("-1")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var flag := false;
  var a := 0;
  var b := 0;
  var i := 1;
  while i <= n && !flag
    invariant 1 <= i
    decreases n - i
  {
    var j := 1;
    while j <= n && !flag
      invariant 1 <= j
      decreases n - j
    {
      if i % j == 0 && i * j > n && i % j < n {
        a := i;
        b := j;
        flag := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  if flag {
    output := IntToString(a) + " " + IntToString(b) + "\n";
  } else {
    output := "-1\n";
  }
}
