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

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}

function ParseIntList(ss: seq<string>): seq<int>
  decreases |ss|
{
  if |ss| == 0 then [] else [ParseInt(ss[0])] + ParseIntList(ss[1..])
}


method Solve(n_str: string, a_list_str: string) returns (output: string)
{
  var nums := ParseIntList(SplitWs(a_list_str));
  var left: map<int, int> := map[];
  var i := 0;
  while i < |nums|
    decreases |nums| - i
  {
    var v := nums[i];
    if v in left {
      left := left[v := left[v] + 1];
    } else {
      left := left[v := 1];
    }
    i := i + 1;
  }
  var done: set<int> := {};
  var count := 0;
  i := 0;
  while i < |nums|
    decreases |nums| - i
  {
    var v := nums[i];
    left := left[v := left[v] - 1];
    if left[v] == 0 {
      left := left - {v};
    }
    if v !in done {
      count := count + |left|;
      done := done + {v};
    }
    i := i + 1;
  }
  output := IntToString(count);
}
