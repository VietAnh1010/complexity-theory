// 1208_B. Uniqueness  (problem 2650, solution 2650_97)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def b_uniqueness(arr):
//     i = 0
//     j = len(arr) - 1
// 
//     last_pos = {}
//     for ind, elem in enumerate(arr):
//         last_pos[elem] = ind
// 
//     repeated_set = set()
//     while arr[j] not in repeated_set:
//         repeated_set.add(arr[j])
//         j -= 1
// 
//     repeated_set.clear()
//     ans = j + 1
//     while arr[i] not in repeated_set:
//         repeated_set.add(arr[i])
//         j = max(j, last_pos[arr[i]])
//         ans = min(ans, j - i)
//         i += 1
//         if i == len(arr):
//             break
//     return ans
//  
// num_elem = int(input())
// elem = input().split(" ")
// 
// print(b_uniqueness(elem))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 25 * n + 16 + |output|
{
  steps := 1;
  var lastPos: map<int, int> := map[];
  var idx := 0;
  ghost var s0 := steps;
  while idx < n
    invariant 0 <= idx <= n
    invariant steps <= s0 + 5 * idx
    invariant forall kk :: 0 <= kk < idx ==> a_list[kk] in lastPos
    decreases n - idx
  {
    steps := steps + 5;
    lastPos := lastPos[a_list[idx] := idx];
    idx := idx + 1;
  }
  assert forall kk :: 0 <= kk < n ==> a_list[kk] in lastPos;
  var j := n - 1;
  var repeated: set<int> := {};
  ghost var s1 := steps;
  while j >= 0 && a_list[j] !in repeated
    invariant -1 <= j < n
    invariant steps <= s1 + 8 * (n - 1 - j)
    decreases j
  {
    steps := steps + 8;
    repeated := repeated + {a_list[j]};
    j := j - 1;
  }
  steps := steps + 10;
  repeated := {};
  var ans := j + 1;
  var i := 0;
  var doneFlag := false;
  ghost var s2 := steps;
  while !doneFlag && a_list[i] !in repeated
    invariant 0 <= i <= n
    invariant !doneFlag ==> i < n
    invariant steps <= s2 + 12 * i
    invariant forall kk :: 0 <= kk < n ==> a_list[kk] in lastPos
    decreases n - i
  {
    steps := steps + 12;
    repeated := repeated + {a_list[i]};
    var lp := lastPos[a_list[i]];
    if lp > j { j := lp; }
    var cand := j - i;
    if cand < ans { ans := cand; }
    i := i + 1;
    if i == n { doneFlag := true; }
  }
  IntToStringDigits(ans);
  steps := steps + 3 + Digits(ans);
  output := IntToString(ans);
}
