// 1108_A. Two distinct points  (problem 936, solution 936_772)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// q = int(input())
// for i in range(q):
//     l1,r1,l2,r2 = input().split()
//     l1=int(l1)
//     l2=int(l2)
//     r1=int(r1)
//     r2=int(r2)
//     if l1 != l2:
//         print (l1,l2)
//     elif l1 != r2:
//         print (l1,r2)
//     elif r1 != l2:
//         print (r1,l2)
//     elif r1 != r2:
//         print (r1,r2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, grid: seq<seq<int>>) returns (output: string)
{
  output := "";
  var i := 0;
  while i < |grid|
    decreases |grid| - i
  {
    var row := grid[i];
    var l1 := row[0];
    var r1 := row[1];
    var l2 := row[2];
    var r2 := row[3];
    if l1 != l2 {
      output := output + IntToString(l1) + " " + IntToString(l2) + "\n";
    } else if l1 != r2 {
      output := output + IntToString(l1) + " " + IntToString(r2) + "\n";
    } else if r1 != l2 {
      output := output + IntToString(r1) + " " + IntToString(l2) + "\n";
    } else if r1 != r2 {
      output := output + IntToString(r1) + " " + IntToString(r2) + "\n";
    }
    i := i + 1;
  }
}
