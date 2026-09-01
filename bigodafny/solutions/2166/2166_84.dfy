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

method Solve(n: int, k: int, numbers: seq<int>) returns (output: string)
{
  var count := 0;
  var i := 0;
  while i < |numbers|
    decreases |numbers| - i
  {
    if 5 - numbers[i] >= k { count := count + 1; }
    i := i + 1;
  }
  output := IntToString(FloorDiv(count, 3));
}
