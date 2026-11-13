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

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |a_list| == n
  // Python wraps a negative subscript; 152 occur across the stored tests.
  requires forall k :: 0 <= k < n ==> -n <= a_list[k] - 1 < n
  ensures steps <= 2 * NLogN(n) + 20 * n + 2 * |output| + 20
{
  steps := 1;
  var up := seq(n, i requires 0 <= i < n => 1 + i*20001);
  var down := seq(n, i requires 0 <= i < n => up[n-1-i]);
  // argsort: sorted [(l, i) for i, l in enumerate(lis)]
  steps := steps + 3 * n + 3;
  var tpls := seq(n, i requires 0 <= i < n => (a_list[i], i));
  var less := (p: (int, int), q: (int, int)) => p.0 < q.0 || (p.0 == q.0 && p.1 < q.1);
  var arg := Sort(tpls, less);
  steps := steps + SortCost(n);
  SortCostWithin(n, n);
  SortIsPermutation(tpls, less);
  forall j | 0 <= j < |arg| ensures exists k :: 0 <= k < n && arg[j] == tpls[k] {
    assert arg[j] in multiset(arg);
    assert arg[j] in tpls;
  }
  var j := 0;
  while j < n
    invariant 0 <= j <= n
    invariant |up| == n
    invariant steps <= 2 * NLogN(n) + 3 * n + 5 + 8 * j
    decreases n - j
  {
    steps := steps + 8;
    var val := PyIndex(arg[j].0 - 1, |up|);
    up := up[val := up[val] + arg[j].1];
    j := j + 1;
  }
  output := JoinInts(up, " ") + "\n" + JoinInts(down, " ") + "\n";
  if n >= 1 {
    JoinIntsLen(up, " ");
    JoinIntsLen(down, " ");
    steps := steps + SumDigits(up) + n + SumDigits(down) + n + 1 + (SumDigits(down) + n) + 1;
  } else {
    steps := steps + 3;
  }
}
