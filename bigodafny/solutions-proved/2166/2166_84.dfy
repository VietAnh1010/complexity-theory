// 432_A. Choosing Teams  (problem 2166, solution 2166_84)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # cook your dish here
// n, k = map(int,input().split())
// a = list(map(int,input().split()))
// 
// count = 0
// 
// for i in a:
//     if(5-i>=k):
//         count+=1
// 
// print(count//3)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(n) -- agrees. One pass, constant work per element.
method Solve(n: int, k: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 5 * |numbers| + 4
{
  steps := 1;
  var count := 0;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant steps == 5 * i + 1
    decreases |numbers| - i
  {
    if 5 - numbers[i] >= k { count := count + 1; }
    i := i + 1;
    steps := steps + 5;
  }
  output := IntToString(FloorDiv(count, 3));
  steps := steps + 3;
}
