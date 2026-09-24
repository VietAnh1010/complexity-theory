// 984_A. Game  (problem 187, solution 187_762)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def sort(n,a):
//     list = a
//     for i in range(0,n):
//         for j in range(0,n):
//             if(list[i]>list[j]):
//                 t = list[i]
//                 list[i] = list[j]
//                 list[j] = t
//     return list
// def erase(n,a):
//     temp=1
//     list = sort(n,a)
//     t=0
//     print(a[(n)//2])
// n = int(input())
// a = [int(i) for i in input().split()]
// erase(n,a)
//
//
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires n >= 1
  ensures steps <= 1 + n * (8 * n + 1) + 2
{
  var arr := a_list;
  steps := 1;
  ghost var obase := steps;
  ghost var Kout := 8 * n + 1;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |arr| == n
    invariant steps <= obase + i * Kout
    decreases n - i
  {
    ghost var i_old := i;
    ghost var ibase := steps;
    var j := 0;
    while j < n
      invariant 0 <= j <= n
      invariant |arr| == n
      invariant steps <= ibase + 8 * j
      decreases n - j
    {
      // arr[i], arr[j], and the comparison itself.
      steps := steps + 3;
      if arr[i] > arr[j] {
        var tmp := arr[i];
        arr := arr[i := arr[j]];
        arr := arr[j := tmp];
        steps := steps + 4;
      }
      j := j + 1;
      steps := steps + 1;
    }
    i := i + 1;
    steps := steps + 1;
    assert steps <= ibase + 8 * n + 1;
    assert steps <= obase + i_old * Kout + Kout;
    CostMulDistrib(i_old, 1, i_old + 1, Kout);
    assert steps <= obase + i * Kout;
  }
  var idx := n / 2;
  output := IntToString(arr[idx]);
  steps := steps + 2;
}
