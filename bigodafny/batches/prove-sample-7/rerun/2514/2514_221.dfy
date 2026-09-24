// 1084_B. Kvass and the Fair Nut  (problem 2514, solution 2514_221)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = list(map(int,input().split()))
// s = n[1]
// n = n[0]
// a = list(map(int,input().split()))
//
// a = sorted(a,reverse = True)
// k = min(a)
// su = 0
// if s > sum(a):
//     print(-1)
// else:
//     for i in range(len(a)):
//         if a[i] > k:
//             su += (a[i]-k)
//             a[i] = k
//             if su >= s:
//                 break
//     if su < s:
//         k = (n*k-(s-su))//n
//         print(k)
//     else:
//         print(k)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |c_list| >= 1
  requires a >= 1
  ensures steps <= 2 * NLogN(|c_list|) + 8 * |c_list| + 20
{
  steps := 1;
  var arr := Sort(c_list, (x: int, y: int) => x > y);
  steps := steps + SortCost(|c_list|);
  SortCostWithin(|c_list|, |c_list|);
  var kk := MinSeq(c_list);
  steps := steps + |c_list|;
  var su := 0;
  var total := SumSeq(c_list);
  steps := steps + |c_list|;
  if b > total {
    output := "-1";
    steps := steps + 1;
  } else {
    var i := 0;
    while i < |arr| && su < b
      invariant 0 <= i <= |arr|
      invariant |arr| == |c_list|
      invariant steps <= 2 * NLogN(|c_list|) + 4 * |c_list| + 3 + 3 * i
      decreases |arr| - i
    {
      if arr[i] > kk {
        su := su + (arr[i] - kk);
        arr := arr[i := kk];
      }
      i := i + 1;
      steps := steps + 3;
    }
    if su < b {
      var res := FloorDiv(a * kk - (b - su), a);
      output := IntToString(res);
    } else {
      output := IntToString(kk);
    }
    steps := steps + 3;
  }
}
