// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The inner `while v != 0` loop and the following `Sort(res, ...)`
//     both operate on `res`, whose length is bounded by the number of
//     decimal digits of a value <=10^4 (at most 5) per the problem
//     statement, so each of the n test cases costs O(1) and the total is
//     O(n), not O(nlogn); the Python shows the identical bound via
//     `res.sort(reverse=True)` on the same digit list.
//
//   how this label could be wrong, and what to check:
//     The label assumes the per-test Sort call scales with n. Check that
//     `res` never holds more than one entry per decimal digit of
//     a_list[t]; since a_list[t] <= 10^4 per the problem statement, |res|
//     <= 5 always, so Sort(res,...) is O(1) regardless of how many test
//     cases n there are.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 34, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "JoinInts"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 1352_A. Sum of Round Numbers  (problem 1263, solution 1263_1960)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// import sys
// 
// ip = lambda : sys.stdin.readline()
// ipl = lambda : sys.stdin.readline().split()
// 
// for _ in range(int(ip())):
// 	n = int(input())
// 	res = []
// 	k = 1
// 	while n:
// 		if n % 10 != 0:
// 			res.append(n%10 * k)
// 		n //= 10
// 		k *= 10
// 	print(len(res))
// 	res.sort(reverse=True)
// 	print(*res)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  requires forall k :: 0 <= k < n ==> a_list[k] >= 1
{
{

  var results: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    decreases n - t
  {
    var v := a_list[t];
    var res: seq<int> := [];
    var kk := 1;
    while v != 0
      invariant v >= 0
      decreases v
    {
      var d := v % 10;
      if d != 0 {
        res := res + [d * kk];
      }
      v := v / 10;
      kk := kk * 10;
    }
    var sorted := Sort(res, (x: int, y: int) => x > y);
    results := results + [IntToString(|res|), JoinInts(sorted, " ")];
    t := t + 1;
  }
  output := Join(results, "\n");
}
}
