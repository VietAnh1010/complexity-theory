// 299_B. Ksusha the Squirrel  (problem 641, solution 641_31)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=list(map(int,input().split()))
// a=input().split('.')
// u=0
// for i in range(len(a)):
//     if '#' in a[i]:
//         if len(a[i])+1>k:
//             print('NO')
//             u+=1
//             break
//     if u>0:
//         break
// if u==0:
//     print('YES')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * |s| + 6
{
  steps := 1;
  var segments, sSteps := SplitByDot(s);
  steps := steps + sSteps;
  var found := false;
  var i := 0;
  while i < |segments| && !found
    invariant 0 <= i <= |segments|
    invariant steps <= 1 + sSteps + 2 * i
    decreases |segments| - i
  {
    if |segments[i]| > 0 && |segments[i]| + 1 > m {
      found := true;
    }
    i := i + 1;
    steps := steps + 2;
  }
  if found {
    output := "NO";
  } else {
    output := "YES";
  }
  steps := steps + 1;
}

method SplitByDot(s: string) returns (parts: seq<string>, ghost steps: nat)
  ensures steps <= 2 * |s| + 2
  ensures |parts| <= |s| + 1
{
  parts := [];
  steps := 1;
  var cur := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant steps == 2 * i + 1
    invariant |parts| <= i
    decreases |s| - i
  {
    if s[i] == '.' {
      parts := parts + [cur];
      cur := "";
    } else {
      cur := cur + [s[i]];
    }
    i := i + 1;
    steps := steps + 2;
  }
  parts := parts + [cur];
  steps := steps + 1;
}
