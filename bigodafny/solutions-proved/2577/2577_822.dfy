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

method Solve(n: int, mat: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n <= |mat|
  requires forall k :: 0 <= k < |mat| ==> |mat[k]| >= 3
  ensures steps <= 12 * |mat| + 3 + 2 * |output|
{
  steps := 1;
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= (if n > 0 then n else 0)
    invariant |lines| == i
    invariant steps == 1 + 12 * i + SumLen(lines)
    decreases n - i
  {
    var row := mat[i];
    var s := row[0] + row[1] + row[2] - 1;
    IntToStringDigits(s);
    SumLenSnoc(lines, IntToString(s));
    lines := lines + [IntToString(s)];
    steps := steps + 12 + Digits(s);
    i := i + 1;
  }
  output := Join(lines, "\n");
  if n > 0 { JoinLen(lines, "\n"); }
  steps := steps + SumLen(lines) + |lines|;
}
