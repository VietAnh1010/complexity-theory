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

// Label O(n*m). Each `mas[i]` is one page interval -- two numbers -- and the
// body reads intervals[i][0] and intervals[i][1] only. Cost per row is constant
// whatever the row's width, so the honest bound is O(n). The loop also breaks at
// the first containing interval, so n is a worst case the data usually beats.
//
// The bound is stated with a clamp rather than `requires n >= 1`: the row
// answers a non-positive n perfectly well (the loop never runs) and a
// precondition would exclude inputs it handles -- the mistake 1254_187 carried.
method Solve(n: int, intervals: seq<seq<int>>, value: int) returns (output: string, ghost steps: nat)
  ensures steps <= 7 * (if n > 0 then n else 0) + 3
{
  steps := 2;
  output := "";
  var i := 0;
  var found := false;
  while i < n && !found
    invariant 0 <= i
    invariant i > 0 ==> i <= n
    invariant steps == 7 * i + 2
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
    steps := steps + 7;
  }
}
