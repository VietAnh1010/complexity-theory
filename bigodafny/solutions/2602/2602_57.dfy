// 1351_A. A+B (Trial Problem)  (problem 2602, solution 2602_57)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// testcase = int(input())
// 
// for i in range(testcase):
//    list1 = list(map(int , input().split()))
//    sum1 = sum(list1)
//    print(sum1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(N: int, pairs_list: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < |pairs_list|
    invariant 0 <= i <= |pairs_list|
    decreases |pairs_list| - i
  {
    lines := lines + [IntToString(SumSeq(pairs_list[i]))];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
