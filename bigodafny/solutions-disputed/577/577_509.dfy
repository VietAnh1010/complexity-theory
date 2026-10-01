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

method Solve(n: int, numbers_list: seq<int>) returns (output: string)
  // all Dfs needs is a non-negative argument. The earlier attempt asked for
  // the problem's full stated range 1..1e9, which 3 stored inputs exceed.
  requires forall t :: 0 <= t < |numbers_list| ==> numbers_list[t] >= 0
{

  var check := [2];
  var i := 0;
  while check[|check| - 1] <= 1000000000
    invariant |check| >= 1
    invariant check[0] == 2
    invariant forall t :: 0 <= t < |check| ==> check[t] >= 2
  {
    check := check + [check[|check| - 1] + 3 * i + 5];
    i := i + 1;
  }
  var results: seq<string> := [];
  var k := 0;
  while k < |numbers_list|
    invariant 0 <= k <= |numbers_list|
    decreases |numbers_list| - k
  {
    results := results + [IntToString(Dfs(check, numbers_list[k]))];
    k := k + 1;
  }
  output := Join(results, "\n");
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
