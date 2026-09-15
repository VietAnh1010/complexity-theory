// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-04
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Every loop in Solve is bounded by the literal constant 31
//     (idxFill<31, i<30, j from 30 down to 0), not by n, which itself the
//     requires clause caps at 31; Python's source uses the same fixed N=31
//     ranges regardless of n, so both are O(1), not O(n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 54, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 3, "recursive_helpers": 1, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 913_C. Party Lemonade  (problem 514, solution 514_39)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// N = 31
// n, l = map(int, input().split())
// cost = [int(x) for x in input().split()]
// for i in range(n, N):
// 	cost.append(math.inf)
// for i in range(N - 1):
// 	cost[i + 1] = min(cost[i + 1], cost[i] * 2)
// # print(cost)
// ans = math.inf
// cur_cost = 0
// for i in range(N - 1, -1, -1):
// 	# print('l = {}'.format(l))
// 	if 2**i >= l:
// 		ans = min(ans, cur_cost + cost[i])
// 	else:
// 		cur_cost += cost[i]
// 		l -= 2**i;
// 	# print('at {} and ans = {}'.format(i, ans))
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, total_score: int, scores: seq<int>) returns (output: string)
  requires 0 <= n <= 31
  requires |scores| == n
{
  var INF := 1000000000000000000;
  var l := total_score;
  var cost: seq<int> := scores;
  var idxFill := n;
  while idxFill < 31
    invariant n <= idxFill <= 31
    invariant |cost| == idxFill
    decreases 31 - idxFill
  {
    cost := cost + [INF];
    idxFill := idxFill + 1;
  }
  var i := 0;
  while i < 30
    invariant 0 <= i <= 30
    invariant |cost| == 31
    decreases 30 - i
  {
    var doubled := cost[i] * 2;
    cost := cost[i + 1 := if cost[i+1] < doubled then cost[i+1] else doubled];
    i := i + 1;
  }
  var ans := INF;
  var cur_cost := 0;
  var ll := l;
  var j := 30;
  while j >= 0
    invariant -1 <= j <= 30
    invariant |cost| == 31
    decreases j + 1
  {
    if Pow2_39(j) >= ll {
      var cand := cur_cost + cost[j];
      ans := if cand < ans then cand else ans;
    } else {
      cur_cost := cur_cost + cost[j];
      ll := ll - Pow2_39(j);
    }
    j := j - 1;
  }
  output := IntToString(ans) + "\n";
}

function Pow2_39(e: int): int
  requires e >= 0
  decreases e
{
  if e == 0 then 1 else 2 * Pow2_39(e - 1)
}
