// 1165_A. Remainder  (problem 1622, solution 1622_305)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
//     n, x, y = map(int, input().split())
//     number = list(input())
//     count = 0
//     i = 0
//     while i < y:
//         if number[-i - 1] != '0':
//             count += 1
//             number[-i - 1] = '0'
//         i += 1
//     i += 1
//     if number[-y - 1] == "0":
//         number[-y -1] = "1"
//         count += 1
//     while i < x:
//         if number[-i - 1] != '0':
//             count += 1
//             number[-i - 1] = '0'
//         i += 1
//     print(count)
// 
// 
// 
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, d: int, binary_list: seq<string>) returns (output: string)
{
  var arr := binary_list;
  var len := |arr|;
  var count := 0;
  var i := 0;
  while i < d
    decreases d - i
  {
    var pos := len - i - 1;
    if arr[pos] != "0" {
      count := count + 1;
      arr := arr[pos := "0"];
    }
    i := i + 1;
  }
  i := i + 1;
  var pos2 := len - d - 1;
  if arr[pos2] == "0" {
    arr := arr[pos2 := "1"];
    count := count + 1;
  }
  while i < k
    decreases k - i
  {
    var pos3 := len - i - 1;
    if arr[pos3] != "0" {
      count := count + 1;
      arr := arr[pos3 := "0"];
    }
    i := i + 1;
  }
  output := IntToString(count);
}
