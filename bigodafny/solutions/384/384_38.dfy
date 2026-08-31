// 59_B. Fortune Telling  (problem 384, solution 384_38)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// input_list = list(map(int,input().split()))
// input_list.sort()
// x = sum(input_list)
// if(x%2 ==1):
//     print(x)
// else:
//     for i in range(n):
//         if(input_list[i]%2 == 1):
//             print(x-input_list[i])
//             break
//     else:
//         print(0)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function SumSeq(xs: seq<int>): int
  decreases |xs|
{
  if |xs| == 0 then 0 else xs[0] + SumSeq(xs[1..])
}

method Solve(v_0: int, v_1: seq<int>) returns (output: string)
{
  var arr := SortInts(v_1);
  var total := SumSeq(arr);
  if total % 2 == 1 {
    output := IntToString(total);
  } else {
    var found := false;
    var ans := 0;
    var i := 0;
    while i < |arr| && !found
      decreases |arr| - i
    {
      if arr[i] % 2 == 1 {
        ans := total - arr[i];
        found := true;
      }
      i := i + 1;
    }
    output := if found then IntToString(ans) else "0";
  }
}
