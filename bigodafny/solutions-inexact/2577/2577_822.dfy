// 1422_A. Fence  (problem 2577, solution 2577_822)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// 
// T = int(input())
// 
// #lets = 'abcdefghijklmnopqrstuvwxyz'
// #key = {lets[i]:i for i in range(26)}
// 
// for t in range(T):
//   #n = int(input())
//   a,b,c = map(int,input().split())
//   #a = list(map(int,input().split()))
//   #a = input()
//   d = False
//   print(a+b+c-1)
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
    var row := mat[i];
    var s := row[0] + row[1] + row[2] - 1;
    lines := lines + [IntToString(s)];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
