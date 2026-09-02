// 952_C. Ravioli Sort  (problem 1765, solution 1765_40)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// size = int(input())
// data = [int(x) for x in input().split()]
// error = False
// while size > 1:
//     for i in range(size - 1):
//         if abs(data[i] - data[i+1]) >= 2:
//             error = True
//     data.remove(max(data))
//     size -= 1
// print("NO" if error else "YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var size := n;
  var data := a_list;
  var error := false;
  while size > 1
    decreases size
  {
    var i := 0;
    while i < size - 1
      decreases size - 1 - i
    {
      if AbsInt(data[i] - data[i + 1]) >= 2 {
        error := true;
      }
      i := i + 1;
    }
    var mx := MaxSeq(data);
    var idx := 0;
    while idx < size && data[idx] != mx
      decreases size - idx
    {
      idx := idx + 1;
    }
    data := data[0..idx] + data[idx + 1..];
    size := size - 1;
  }
  output := if error then "NO" else "YES";
}
