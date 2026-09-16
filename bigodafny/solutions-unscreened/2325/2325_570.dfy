// 1337_A. Ichihime and Triangle  (problem 2325, solution 2325_570)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input = sys.stdin.readline
// 
// def inp():
//     return(int(input()))
// def inlt():
//     return(list(map(int,input().split())))
// def insr():
//     s = input()
//     return(list(s[:len(s) - 1]))
// def invr():
//     return(map(int,input().split()))
// 
// tests = inp()
// testcount = 0
// while testcount < tests:
//     a,b,c,d = invr()
//     print(b,c,c)
//     testcount += 1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var row := lists[i];
    var b := row[1];
    var c := row[2];
    parts := parts + [IntToString(b) + " " + IntToString(c) + " " + IntToString(c)];
    i := i + 1;
  }
  output := Join(parts, "\n");
}
