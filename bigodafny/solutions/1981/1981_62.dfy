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
{
  output := ""; // TODO: translate the Python above
}
