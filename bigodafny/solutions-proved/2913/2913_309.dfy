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

// Isolated multiplication: bumping the outer progress count by 1 adds
// exactly the constant per-outer-iteration cost c.
lemma DistribStep(a: int, c: int)
  ensures (a + 1) * c == a * c + c
{}

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= (if n > 0 then n else 0) * (4 * (if n > 0 then n else 0) + 6) + 10
{
  steps := 1;
  var flag := false;
  var a := 0;
  var b := 0;
  var i := 1;
  ghost var nn := if n > 0 then n else 0;
  ghost var base1 := steps;
  while i <= n && !flag
    invariant 1 <= i
    invariant i - 1 <= nn
    invariant steps <= base1 + (i - 1) * (4 * nn + 6)
    decreases n - i
  {
    var j := 1;
    ghost var base2 := steps;
    while j <= n && !flag
      invariant 1 <= j
      invariant j - 1 <= nn
      invariant steps <= base2 + 4 * (j - 1)
      decreases n - j
    {
      if i % j == 0 && i * j > n && i % j < n {
        a := i;
        b := j;
        flag := true;
      }
      j := j + 1;
      steps := steps + 4;
    }
    DistribStep(i - 1, 4 * nn + 6);
    i := i + 1;
    steps := steps + 2;
  }
  if flag {
    output := IntToString(a) + " " + IntToString(b) + "\n";
  } else {
    output := "-1\n";
  }
  steps := steps + 2;
}
