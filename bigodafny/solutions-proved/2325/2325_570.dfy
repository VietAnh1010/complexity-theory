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

method Solve(n: int, lists: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n <= |lists|
  requires forall k :: 0 <= k < |lists| ==> |lists[k]| >= 4
  ensures steps <= 12 * (if n > 0 then n else 0) + 4 + 3 * |output|
{
  steps := 1;
  var parts: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n || n < 0
    invariant i >= 0 && (n >= 0 ==> i <= n) && (n < 0 ==> i == 0)
    invariant |parts| == i
    invariant steps <= 1 + 10 * i + 2 * SumLen(parts)
    decreases n - i
  {
    var row := lists[i];
    var b := row[1];
    var c := row[2];
    ghost var e := IntToString(b) + " " + IntToString(c) + " " + IntToString(c);
    IntToStringDigits(b);
    IntToStringDigits(c);
    steps := steps + 10 + Digits(b) + 2 * Digits(c) + Digits(c) + Digits(b) + Digits(c);
    SumLenSnoc(parts, e);
    parts := parts + [IntToString(b) + " " + IntToString(c) + " " + IntToString(c)];
    i := i + 1;
  }
  output := Join(parts, "\n");
  if |parts| >= 1 { JoinLen(parts, "\n"); }
  steps := steps + SumLen(parts) + |parts|;
}
