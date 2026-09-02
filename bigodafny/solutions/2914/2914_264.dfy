// 1136_A. Nastya Is Reading a Book  (problem 2914, solution 2914_264)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// mas =  []
// 
// for i in range(n):
//     c = list(map(int,input().split()))
//     mas.append(c)
// 
// k = int(input())
// 
// for i in range(n):
//     if k >= mas[i][0] and k <= mas[i][1]:
//         print(n-i)
//         break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, intervals: seq<seq<int>>, value: int) returns (output: string)
{
  output := "";
  var i := 0;
  var found := false;
  while i < n && !found
    invariant 0 <= i
    decreases if found then 0 else n - i
  {
    if i < |intervals| && |intervals[i]| >= 2 {
      var lo := intervals[i][0];
      var hi := intervals[i][1];
      if value >= lo && value <= hi {
        output := IntToString(n - i);
        found := true;
      }
    }
    i := i + 1;
  }
}
