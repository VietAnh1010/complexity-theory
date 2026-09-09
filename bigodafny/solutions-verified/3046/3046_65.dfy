// 595_A. Vitaly and Night  (problem 3046, solution 3046_65)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// l=0
// for i in range(n):
//     arr=list(map(int,input().split()))
//     j=1
//     while j<len(arr):
//         if arr[j-1]==1 or arr[j]==1:
//             l+=1
//         j+=2
// print(l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// Label O(n*m), and here it is RIGHT. The inner loop walks the whole row, so a
// wider row really does cost more: the bound carries a genuine second dimension,
// the total number of seats. TotalLen(v_3) is n*m when every row has width m.
//
// Contrast the sibling findings in this directory: 1650_428, 2719_94, 396_361,
// 525_273 and 2914_264 all carry the same label while reading a fixed number of
// positions per row. The label is not wrong as a rule -- it is wrong when the
// body never scans a row.
ghost function TotalLenUpTo(rows: seq<seq<int>>, k: nat): nat
  requires k <= |rows|
{
  if k == 0 then 0 else TotalLenUpTo(rows, k - 1) + |rows[k - 1]|
}

method Solve(n: int, m: int, v_3: seq<seq<int>>) returns (output: string, ghost steps: nat)
  ensures steps <= 6 * |v_3| + 2 * TotalLenUpTo(v_3, |v_3|) + 3
{
  steps := 1;
  var l := 0;
  var i := 0;
  while i < |v_3|
    invariant 0 <= i <= |v_3|
    invariant steps <= 6 * i + 2 * TotalLenUpTo(v_3, i) + 1
    decreases |v_3| - i
  {
    ghost var s0 := steps;
    var arr := v_3[i];
    var j := 1;
    while j < |arr|
      invariant 1 <= j
      invariant j == 1 || j <= |arr| + 1
      invariant steps == s0 + 2 * j - 2
      decreases |arr| - j
    {
      if arr[j - 1] == 1 || arr[j] == 1 {
        l := l + 1;
      }
      j := j + 2;
      steps := steps + 4;
    }
    assert steps <= s0 + 2 * |arr|;
    assert |arr| == |v_3[i]|;
    i := i + 1;
    steps := steps + 6;
  }
  output := IntToString(l);
  steps := steps + 2;
}
