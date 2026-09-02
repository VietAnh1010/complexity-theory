// 886_C. Petya and Catacombs  (problem 2505, solution 2505_87)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// arr = list(map(int, input().split()))
// arr.sort()
// cnt_total = 0
// cnt_tmp = 0
// for i in range(1,n):
//     if arr[i] == arr[i-1]:
//         cnt_total +=1
// print(cnt_total+1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<seq<int>>) returns (output: string)
{
  var arr := SortInts(coordinates[0]);
  var cnt := 0;
  var i := 1;
  while i < n
    decreases n - i
  {
    if arr[i] == arr[i - 1] {
      cnt := cnt + 1;
    }
    i := i + 1;
  }
  output := IntToString(cnt + 1);
}
