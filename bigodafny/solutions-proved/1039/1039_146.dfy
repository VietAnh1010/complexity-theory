// 1004_C. Sonya and Robots  (problem 1039, solution 1039_146)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// nums = list(map(int, input().split()))
// left = {}
// from collections import Counter
// left=Counter(nums)
// count = 0
// done = set()
// for i in nums:
//     left[i] -= 1
//     if left[i] == 0:
//         del left[i]
//     if i not in done:
//         count += len(left.keys())
//         done.add(i)
// 
// print(count)
// 	
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude


method Solve(n_str: string, a_list_str: string) returns (output: string, ghost steps: nat)
  ensures steps <= 22 * |ParseInts(SplitWs(a_list_str))| + |n_str| + |a_list_str| + |output| + 6
{
  var nums := ParseInts(SplitWs(a_list_str));
  steps := 1 + |n_str| + |a_list_str|;
  var left: map<int, int> := map[];
  var i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant steps <= 1 + |n_str| + |a_list_str| + 10 * i
    invariant forall x :: (x in left <==> Occ1039(nums, 0, i, x) > 0)
    invariant forall x :: x in left ==> left[x] == Occ1039(nums, 0, i, x)
    decreases |nums| - i
  {
    var v := nums[i];
    if v in left {
      left := left[v := left[v] + 1];
    } else {
      left := left[v := 1];
    }
    i := i + 1;
    steps := steps + 10;
  }
  assert forall x :: Occ1039(nums, 0, |nums|, x) == Occ1039(nums, 0, i, x);
  var done: set<int> := {};
  var count := 0;
  i := 0;
  while i < |nums|
    invariant 0 <= i <= |nums|
    invariant steps <= 1 + |n_str| + |a_list_str| + 10 * |nums| + 12 * i
    invariant forall x :: (x in left <==> Occ1039(nums, i, |nums|, x) > 0)
    invariant forall x :: x in left ==> left[x] == Occ1039(nums, i, |nums|, x)
    decreases |nums| - i
  {
    var v := nums[i];
    forall x ensures Occ1039(nums, i, |nums|, x) == (if nums[i] == x then 1 else 0) + Occ1039(nums, i + 1, |nums|, x) {
      Occ1039Front(nums, i, |nums|, x);
    }
    left := left[v := left[v] - 1];
    if left[v] == 0 {
      left := left - {v};
    }
    if v !in done {
      count := count + |left|;
      done := done + {v};
    }
    i := i + 1;
    steps := steps + 12;
  }
  output := IntToString(count);
  IntToStringDigits(count);
  steps := steps + 1 + |output|;
}

ghost function Occ1039(s: seq<int>, lo: int, hi: int, x: int): nat
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if hi == lo then 0 else Occ1039(s, lo, hi - 1, x) + (if s[hi - 1] == x then 1 else 0)
}

lemma Occ1039Front(s: seq<int>, lo: int, hi: int, x: int)
  requires 0 <= lo < hi <= |s|
  ensures Occ1039(s, lo, hi, x) == (if s[lo] == x then 1 else 0) + Occ1039(s, lo + 1, hi, x)
  decreases hi - lo
{
  if hi > lo + 1 { Occ1039Front(s, lo, hi - 1, x); }
}
