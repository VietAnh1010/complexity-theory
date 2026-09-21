// 1041_A. Heist  (problem 603, solution 603_489)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// n=int(input())
// indices=[]
// indices=input().split(' ')
// for i in range(n):
//     indices[i]=int(indices[i])
// minIndic=min(indices)
// maxIndic=max(indices)
// diff=maxIndic-minIndic+1
// if diff<n :
//     x=0
// else:
//     x=diff-n
// print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires |numbers| > 0
  ensures steps <= 5 * |numbers| + 5
{
  var mn := numbers[0];
  var mx := numbers[0];
  var i := 1;
  steps := 1;
  while i < |numbers|
    invariant 1 <= i <= |numbers|
    invariant steps == 5 * (i - 1) + 1
    decreases |numbers| - i
  {
    if numbers[i] < mn { mn := numbers[i]; }
    if numbers[i] > mx { mx := numbers[i]; }
    i := i + 1;
    steps := steps + 5;
  }
  var diff := mx - mn + 1;
  var x := if diff < n then 0 else diff - n;
  output := IntToString(x);
  steps := steps + 3;
}
