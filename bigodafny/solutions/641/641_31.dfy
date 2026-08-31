// 299_B. Ksusha the Squirrel  (problem 641, solution 641_31)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=list(map(int,input().split()))
// 
// 
// 
// a=input().split('.')
// u=0
// 
// 
// 
// for i in range(len(a)):
//     if '#' in a[i]:
//         if len(a[i])+1>k:
//             print('NO')
//             u+=1
//             break
//     if u>0:
//         break
// 
// if u==0:
//     print('YES')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  var segments := SplitByDot(s);
  var found := false;
  var i := 0;
  while i < |segments| && !found
    decreases |segments| - i
  {
    if |segments[i]| > 0 && |segments[i]| + 1 > m {
      found := true;
    }
    i := i + 1;
  }
  if found {
    output := "NO";
  } else {
    output := "YES";
  }
}

method SplitByDot(s: string) returns (parts: seq<string>)
{
  parts := [];
  var cur := "";
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] == '.' {
      parts := parts + [cur];
      cur := "";
    } else {
      cur := cur + [s[i]];
    }
    i := i + 1;
  }
  parts := parts + [cur];
}
