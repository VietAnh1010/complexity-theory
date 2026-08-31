// 186_A. Comparing Strings  (problem 1243, solution 1243_178)
// time complexity: O(n+m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # http://codeforces.com/problemset/problem/186/A
// a = list(input())
// b = list(input())
// ans = 'NO'
// 
// if len(a)==len(b):
//     l = []
//     for i in range(len(a)):
//         if a[i]!= b[i]:
//             l.append(i)
//     if len(l) == 2:
//         a[l[0]],a[l[1]] = a[l[1]], a[l[0]]
//         if a == b:
//             ans = 'YES'
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s1: string, s2: string) returns (output: string)
{
  var ans := "NO";
  if |s1| == |s2| {
    var diffs: seq<int> := [];
    var i := 0;
    while i < |s1|
      decreases |s1| - i
    {
      if s1[i] != s2[i] { diffs := diffs + [i]; }
      i := i + 1;
    }
    if |diffs| == 2 {
      var a := s1;
      var i0 := diffs[0];
      var i1 := diffs[1];
      var tmp := a[i0];
      a := a[i0 := a[i1]];
      a := a[i1 := tmp];
      if a == s2 { ans := "YES"; }
    }
  }
  output := ans;
}
