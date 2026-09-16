// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-07
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The Dafny dedups target values with a nested while loop (`while j <
//     i`) comparing every new entry against all previous entries via
//     signs/nums/dens, an O(n**2) construct with no SortInts call at all;
//     Python instead does target.sort() then itertools.groupby, giving the
//     labelled O(nlogn), so the translation replaced the sort with
//     quadratic pairwise comparison.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 45, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 514_B. Han Solo and Lazer Gun  (problem 1027, solution 1027_141)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import itertools
// 
// n, x0, y0 = [int(x) for x in input().split()]
// target = []
// for i in range(n):
//     x, y = [int(x) for x in input().split()]
//     cos2 = (x-x0)**2 / ((x-x0)**2 + (y-y0)**2)
//     target.append(cos2 if (x-x0)*(y-y0) >= 0 else -cos2)
// 
// target.sort()
// L = list(itertools.groupby(target))
// print(len(L))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<(int, int)>) returns (output: string)
{
  var signs: seq<int> := [];
  var nums: seq<int> := [];
  var dens: seq<int> := [];
  var i := 0;
  while i < |d_list|
    invariant 0 <= i <= |d_list|
    invariant |signs| == i && |nums| == i && |dens| == i
    decreases |d_list| - i
  {
    var dx := d_list[i].0 - b;
    var dy := d_list[i].1 - c;
    var num := dx * dx;
    var den := dx * dx + dy * dy;
    var sgn := if dx * dy >= 0 then 1 else -1;
    signs := signs + [sgn];
    nums := nums + [num];
    dens := dens + [den];
    i := i + 1;
  }
  var count := 0;
  i := 0;
  while i < |d_list|
    invariant 0 <= i <= |d_list|
    decreases |d_list| - i
  {
    var isNew := true;
    var j := 0;
    while j < i
      invariant 0 <= j <= i
      decreases i - j
    {
      if signs[j] == signs[i] && nums[i] * dens[j] == nums[j] * dens[i] {
        isNew := false;
      }
      j := j + 1;
    }
    if isNew { count := count + 1; }
    i := i + 1;
  }
  output := IntToString(count);
}
