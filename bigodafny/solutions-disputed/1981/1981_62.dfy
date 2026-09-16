// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-14
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny loop does `up := up[val := up[val] + i]` for each of n
//     iterations, a seq-update copy costing O(n) per iteration per the
//     prelude cost table, for O(n**2) total, while the Python's cost is
//     dominated by its O(n log n) `sorted(tpls)` call with O(1) list
//     updates thereafter.
//
//   how this label could be wrong, and what to check:
//     The label comes from Python's `sorted(tpls)` in argsort, an O(n log
//     n) sort; the Dafny never sorts and instead updates `up` with `up :=
//     up[val := up[val] + i]` inside a while loop over n. Confirm no Sort
//     call appears anywhere in the Dafny, then check that this seq update,
//     per the cost table, is O(|up|) and runs n times, giving O(n**2)
//     regardless of the missing sort.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 20, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p03938 AtCoder Grand Contest 007 - Construct Sequences  (problem 1981, solution 1981_62)
// time complexity: O(nlogn)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def gen_ordinary_lists(n):
//     up_lis = list(range(1, n * 20001, 20001))
//     return up_lis, up_lis[::-1]
// 
// 
// def argsort(lis):
//     tpls = [(l, i) for i, l in enumerate(lis)]
//     return sorted(tpls)
// 
// 
// def solve(N, lis):
//     up_list, down_list = gen_ordinary_lists(N)
//     arg_tpls = argsort(lis)
//     for val, idx in arg_tpls:
//         up_list[val - 1] += idx
//     print(*up_list)
//     print(*down_list)
//     
// 
// N = int(input())
// lis = list(map(int, input().split()))
// 
// solve(N, lis)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 0
  requires |a_list| == n
  // Python wraps a negative subscript; 152 occur across the stored tests.
  requires forall k :: 0 <= k < n ==> -n <= a_list[k] - 1 < n
{
  var up := seq(n, i requires 0 <= i < n => 1 + i*20001);
  var down := seq(n, i requires 0 <= i < n => up[n-1-i]);
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |up| == n
  {
    var val := PyIndex(a_list[i] - 1, |up|);
    up := up[val := up[val] + i];
    i := i + 1;
  }
  output := JoinInts(up, " ") + "\n" + JoinInts(down, " ") + "\n";
}
