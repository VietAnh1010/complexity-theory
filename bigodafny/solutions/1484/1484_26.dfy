// 172_A. Phone Code  (problem 1484, solution 1484_26)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=[];i=0
// for _ in range(int(input())):l.append(input())
// a=max(l);b=min(l)
// while a[i]==b[i]:i+=1
// print(i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<string>) returns (output: string)
{
  var best := numbers[0];
  var worst := numbers[0];
  var idx := 1;
  while idx < |numbers|
    decreases |numbers| - idx
  {
    if StringLess(best, numbers[idx]) { best := numbers[idx]; }
    if StringLess(numbers[idx], worst) { worst := numbers[idx]; }
    idx := idx + 1;
  }
  var i := 0;
  while i < |best| && i < |worst| && best[i] == worst[i]
    decreases |best| - i
  {
    i := i + 1;
  }
  output := IntToString(i);
}
