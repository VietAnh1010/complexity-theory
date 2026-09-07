// 1095_D. Circular Dance  (problem 2007, solution 2007_4)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// if n == 3:
//     print(3, 2, 1)
//     exit()
// d = []
// d.append([0, 0])
// for i in range(n):
//     x, y = map(int, input().split())
//     d.append([x, y])
// x = 1
// ans = []
// ans.append(1)
// while True:
//     t = d[x][0]
//     if d[t][0] == d[x][1] or d[t][1] == d[x][1]:
//         ans.append(t)
//         ans.append(d[x][1])
//         x = d[x][1]
//     else:
//         ans.append(d[x][1])
//         ans.append(t)
//         x = t
//     if len(ans) >= n:
//         break
// print(*ans[:n])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
  requires n >= 3
  requires |edges| == n
  requires forall k :: 0 <= k < n ==> |edges[k]| >= 2
  requires forall k :: 0 <= k < n ==> 1 <= edges[k][0] <= n && 1 <= edges[k][1] <= n
{
  if n == 3 {
    output := "3 2 1\n";
  } else {
    var d: seq<seq<int>> := [[0,0]];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |d| == i + 1
      invariant forall k :: 1 <= k <= i ==> |d[k]| >= 2 && 1 <= d[k][0] <= n && 1 <= d[k][1] <= n
    {
      d := d + [edges[i]];
      i := i + 1;
    }
    var x := 1;
    var ans: seq<int> := [1];
    var cont := true;
    while cont
      invariant 1 <= x <= n
      invariant |d| == n + 1
      invariant forall k :: 1 <= k <= n ==> |d[k]| >= 2 && 1 <= d[k][0] <= n && 1 <= d[k][1] <= n
      invariant cont == (|ans| < n)
      decreases if |ans| < n then n - |ans| else 0
    {
      var t := d[x][0];
      if d[t][0] == d[x][1] || d[t][1] == d[x][1] {
        ans := ans + [t, d[x][1]];
        x := d[x][1];
      } else {
        ans := ans + [d[x][1], t];
        x := t;
      }
      if |ans| >= n {
        cont := false;
      }
    }
    var res := ans[..n];
    output := JoinInts(res, " ") + "\n";
  }
}
