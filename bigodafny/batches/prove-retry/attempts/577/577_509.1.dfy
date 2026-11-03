// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-u01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the tests in numbers_list and each Dfs call
//     recurses on the VALUE x with depth that depends on x (about log log
//     x levels, each scanning the literal-sized check table), so the cost
//     is O(t log log max x), not O(n) in the test count; the Python's
//     recursive dfy with bisect pays the same depth term.
//
//   how this label could be wrong, and what to check:
//     The label O(n) treats the per-test cost as constant, counting only
//     the t test cases. Check `Dfs(check, numbers_list[k])`: it recurses
//     on the integer x (x - check[idx]), so each test pays a depth that
//     grows with the value x; if you accept that depth as negligible (it
//     is about log log x) the label stands, but the rule counts it.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 48, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 1, "loops": 2, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": true, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1345_B. Card Constructions  (problem 577, solution 577_509)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// check=[2]
// i=0
// while check[-1]<=10**9:
//     check.append(check[-1]+3*i+5)
//     i+=1
// from bisect import bisect_right
// def dfs(x):
//     if x<2:
//         return 0
//     return dfs(x-check[bisect_right(check,x)-1])+1
// for _ in range(int(input())):
//     n=int(input())
//     print(dfs(n))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function FindCost577(check: seq<int>, i: nat): nat
  requires i <= |check|
  decreases |check| - i
{
  if i >= |check| then 1 else 5 + FindCost577(check, i + 1)
}

lemma FindCostBound577(check: seq<int>, i: nat)
  requires i <= |check|
  ensures FindCost577(check, i) <= 5 * (|check| - i) + 1
  decreases |check| - i
{
  if i < |check| { FindCostBound577(check, i + 1); }
}

ghost function DfsCost577(check: seq<int>, x: int): nat
  requires |check| > 0
  requires check[0] == 2
  requires forall t :: 0 <= t < |check| ==> check[t] >= 2
  requires x >= 0
  decreases x
{
  if x < 2 then 2
  else FindCost577(check, 0) + 3 + DfsCost577(check, x - check[FindIdxFrom(check, x, 0, 0)])
}

lemma DfsBound577(check: seq<int>, x: int)
  requires |check| > 0 && |check| <= 200000001
  requires check[0] == 2
  requires forall t :: 0 <= t < |check| ==> check[t] >= 2
  requires x >= 0
  ensures DfsCost577(check, x) <= (x / 2 + 1) * 1200000020
  decreases x
{
  if x >= 2 {
    var idx := FindIdxFrom(check, x, 0, 0);
    var x2 := x - check[idx];
    FindCostBound577(check, 0);
    DfsBound577(check, x2);
    CostMulMonoLeft(x2 / 2 + 1, x / 2, 1200000020);
    CostMulDistrib(1, x / 2, x / 2 + 1, 1200000020);
  }
}

ghost function S577(a: seq<int>, k: nat): nat
  requires k <= |a|
  decreases k
{
  if k == 0 then 0 else S577(a, k - 1) + (if a[k - 1] >= 0 then a[k - 1] / 2 else 0) + 1
}

method Solve(n: int, numbers_list: seq<int>) returns (output: string, ghost steps: nat)
  requires forall t :: 0 <= t < |numbers_list| ==> numbers_list[t] >= 0
  ensures steps <= 2000000100 + 14 * |numbers_list| + 1200000020 * S577(numbers_list, |numbers_list|) + 2 * |output|
{
  steps := 1;
  var check := [2];
  var i := 0;
  while check[|check| - 1] <= 1000000000
    invariant |check| >= 1
    invariant check[0] == 2
    invariant forall t :: 0 <= t < |check| ==> check[t] >= 2
    invariant i == |check| - 1
    invariant check[|check| - 1] >= 2 + 5 * i
    invariant |check| <= 200000001
    invariant steps == 1 + 10 * i
    decreases 1000000001 - check[|check| - 1]
  {
    check := check + [check[|check| - 1] + 3 * i + 5];
    i := i + 1;
    steps := steps + 10;
  }
  var results: seq<string> := [];
  var k := 0;
  ghost var B := steps;
  while k < |numbers_list|
    invariant 0 <= k <= |numbers_list|
    invariant |results| == k
    invariant steps <= B + 14 * k + 1200000020 * S577(numbers_list, k) + SumLen(results)
    decreases |numbers_list| - k
  {
    DfsBound577(check, numbers_list[k]);
    IntToStringDigits(Dfs(check, numbers_list[k]));
    SumLenSnoc(results, IntToString(Dfs(check, numbers_list[k])));
    results := results + [IntToString(Dfs(check, numbers_list[k]))];
    k := k + 1;
    steps := steps + 10 + DfsCost577(check, numbers_list[k - 1]) + |results[k - 1]|;
  }
  if |results| > 0 { JoinLen(results, "\n"); }
  output := Join(results, "\n");
  steps := steps + SumLen(results) + |results|;
}

function FindIdxFrom(check: seq<int>, x: int, i: int, best: int): int
  requires 0 <= i <= |check|
  requires 0 <= best < |check|
  requires check[best] <= x
  decreases |check| - i
  ensures 0 <= FindIdxFrom(check, x, i, best) < |check|
  ensures check[FindIdxFrom(check, x, i, best)] <= x
{
  if i >= |check| then best
  else if check[i] <= x then FindIdxFrom(check, x, i + 1, i)
  else FindIdxFrom(check, x, i + 1, best)
}

function Dfs(check: seq<int>, x: int): int
  requires |check| > 0
  requires check[0] == 2
  requires forall t :: 0 <= t < |check| ==> check[t] >= 2
  requires x >= 0
  decreases x
{
  if x < 2 then 0
  else 1 + Dfs(check, x - check[FindIdxFrom(check, x, 0, 0)])
}
