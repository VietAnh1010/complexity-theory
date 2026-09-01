// 1422_A. Fence  (problem 2577, solution 2577_283)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// import math
// 
// input = sys.stdin.readline
// 
// def inInt():
//     return int(input())
// 
// def inStr():
//     return input().strip("\n")
// 
// def inIList():
//     return (list(map(int, input().split())))
// 
// def inSList():
//     return (input().split())
// 
// #########################################
// 
// def solve(l):
//     print(sum(l) - 1)
// 
// tasks = inInt()
// for t in range(tasks):
//     l = inIList()
//     solve(l)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, mat: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var s := SumSeq(mat[i]) - 1;
    lines := lines + [IntToString(s)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
