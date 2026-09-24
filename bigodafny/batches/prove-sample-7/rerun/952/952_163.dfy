// 977_F. Consecutive Subsequence  (problem 952, solution 952_163)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = [*map(int, input().split())]
// c = [None] * n
// whereIs = [None] * n
// for i in range(0, n):
//     c[i] = i
// c.sort(key=lambda value:a[value])
// tot = 0
// for i in range(0, n):
//     if i == 0 or a[c[i]] != a[c[i - 1]]:
//         whereIs[c[i]] = tot
//         tot += 1
//     else :
//         whereIs[c[i]] = whereIs[c[i - 1]]
// dp = [0] * n
// preState = [None] * n
// lst = [-1] * n
// res = 0
// ptr = -1
// for i in range(0, n):
//     if whereIs[i] == 0:
//         preState[i] = -1
//         dp[i] = 1
//     else:
//         preState[i] = lst[whereIs[i] - 1]
//         if a[preState[i]] != a[i] - 1:
//             preState[i] = -1;
//
//         # print("tset : ", preState[i], end="\n")
//         if preState[i] != -1:
//             dp[i] = dp[preState[i]] + 1
//         else:
//             dp[i] = 1
//
//     lst[whereIs[i]] = i
//     # print(i, " : ", dp[i], " where : ", whereIs[i], end="! \n")
//
//     res = max(res, dp[i])
//     if res == dp[i]:
//         ptr = i
// print(res)
// resArr = [-1] * res
// while res > 0:
//     resArr[res - 1] = ptr + 1
//     ptr = preState[ptr]
//     res -= 1
// print(' '.join(map(str, resArr)))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 2 * NLogN(n) + 20 * n + 15
{
  steps := 1;
  var sortedVals := SortInts(a_list);
  assert |sortedVals| == n;
  steps := steps + SortCost(n);
  var rankMap: map<int, int> := map[];
  var tot := 0;
  var si := 0;
  while si < |sortedVals|
    invariant 0 <= si <= |sortedVals|
    invariant |sortedVals| == n
    invariant 0 <= tot <= si
    invariant si >= 1 ==> tot >= 1
    invariant forall key :: key in rankMap ==> 0 <= rankMap[key] < tot
    invariant steps <= 1 + SortCost(n) + 3 * si
    decreases |sortedVals| - si
  {
    if si == 0 || sortedVals[si] != sortedVals[si - 1] {
      rankMap := rankMap[sortedVals[si] := tot];
      tot := tot + 1;
    }
    si := si + 1;
    steps := steps + 3;
  }
  assert tot >= 1;
  assert tot <= n;

  var whereIs := seq(n, _ => 0);
  var wi := 0;
  while wi < n
    invariant 0 <= wi <= n
    invariant |whereIs| == n
    invariant tot >= 1
    invariant forall key :: key in rankMap ==> 0 <= rankMap[key] < tot
    invariant forall k :: 0 <= k < wi ==> 0 <= whereIs[k] < tot
    invariant steps <= 1 + SortCost(n) + 3 * n + 2 * wi
    decreases n - wi
  {
    whereIs := whereIs[wi := if a_list[wi] in rankMap then rankMap[a_list[wi]] else 0];
    wi := wi + 1;
    steps := steps + 2;
  }
  assert forall k :: 0 <= k < n ==> 0 <= whereIs[k] < tot;
  assert tot <= n;
  assert forall k :: 0 <= k < n ==> 0 <= whereIs[k] < n;

  var dp := seq(n, _ => 0);
  var preState := seq(n, _ => 0);
  var lst := seq(n, _ => -1);
  assert forall k :: 0 <= k < n ==> lst[k] == -1;
  assert forall k :: 0 <= k < n ==> 0 <= whereIs[k] < n;

  var res := 0;
  var ptr := -1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |whereIs| == n && |dp| == n && |preState| == n && |lst| == n
    invariant -1 <= ptr < n
    invariant forall k :: 0 <= k < n ==> lst[k] == -1 || (0 <= lst[k] < i)
    invariant forall k :: 0 <= k < n ==> 0 <= whereIs[k] < n
    invariant forall k :: 0 <= k < i ==> -1 <= preState[k] < k
    invariant forall k :: 0 <= k < i ==> dp[k] >= 1
    invariant forall k :: 0 <= k < i ==> dp[k] <= k + 1
    invariant forall k :: 0 <= k < i && preState[k] != -1 ==> dp[k] == dp[preState[k]] + 1
    invariant forall k :: 0 <= k < i && preState[k] == -1 ==> dp[k] == 1
    invariant ptr == -1 ==> res == 0
    invariant ptr != -1 ==> 0 <= ptr < i && dp[ptr] == res
    invariant steps <= 1 + SortCost(n) + 3 * n + 2 * n + 8 * i
    decreases n - i
  {
    var r := whereIs[i];
    if r == 0 {
      preState := preState[i := -1];
      dp := dp[i := 1];
    } else {
      var pv := lst[r - 1];
      var av := if pv == -1 then a_list[n - 1] else a_list[pv];
      if av != a_list[i] - 1 {
        pv := -1;
      }
      preState := preState[i := pv];
      if pv != -1 {
        dp := dp[i := dp[pv] + 1];
      } else {
        dp := dp[i := 1];
      }
    }
    lst := lst[whereIs[i] := i];
    if dp[i] > res {
      res := dp[i];
    }
    if res == dp[i] {
      ptr := i;
    }
    i := i + 1;
    steps := steps + 8;
  }
  assert res <= n;
  assert steps <= 1 + SortCost(n) + 5 * n + 8 * n;

  var resArr := seq(res, _ => 0);
  var rr := res;
  while rr > 0
    invariant 0 <= rr <= res
    invariant |resArr| == res
    invariant |dp| == n && |preState| == n
    invariant ptr != -1 ==> 0 <= ptr < n && dp[ptr] == rr
    invariant rr == 0 || ptr != -1
    invariant forall k :: 0 <= k < n ==> -1 <= preState[k] < k
    invariant forall k :: 0 <= k < n && preState[k] != -1 ==> dp[k] == dp[preState[k]] + 1
    invariant forall k :: 0 <= k < n && preState[k] == -1 ==> dp[k] == 1
    invariant steps <= 1 + SortCost(n) + 13 * n + 3 * (res - rr)
    decreases rr
  {
    resArr := resArr[rr - 1 := ptr + 1];
    ptr := preState[ptr];
    rr := rr - 1;
    steps := steps + 3;
  }
  assert steps <= 1 + SortCost(n) + 13 * n + 3 * res;
  assert res <= n;
  assert steps <= 1 + SortCost(n) + 16 * n;

  var parts := resArr;
  steps := steps + |parts| + 1;
  assert |parts| == res;
  assert steps <= 2 + SortCost(n) + 16 * n + res;
  SortCostNLogN(n);
  assert steps <= 2 * NLogN(n) + 17 * n + 3;
  output := IntToString(res) + "\n" + JoinInts(parts, " ") + "\n";
  steps := steps + 4;
}
