// 960_A. Check the string  (problem 1368, solution 1368_67)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import defaultdict
// s = list(input())
// t = sorted(s)
// flag = True
// if s[0] != "a":
//     flag = False
// if s != t:
//     flag = False
// dic = defaultdict(int)
// for i in s:
//     dic[i] += 1
//
// if dic["a"] == 0 or dic["b"] == 0:
//     flag = False
//
// if dic["a"] != dic["c"] and dic["b"] != dic["c"]:
//     flag = False
//
// if flag:
//     print("YES")
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string)
{
  var n := |s|;
  var flag := true;
  if n == 0 || s[0] != 'a' { flag := false; }
  var i := 0;
  while i + 1 < n
    decreases n - i
  {
    if s[i] > s[i+1] { flag := false; }
    i := i + 1;
  }
  var ca := 0;
  var cb := 0;
  var cc := 0;
  i := 0;
  while i < n
    decreases n - i
  {
    if s[i] == 'a' { ca := ca + 1; }
    else if s[i] == 'b' { cb := cb + 1; }
    else if s[i] == 'c' { cc := cc + 1; }
    i := i + 1;
  }
  if ca == 0 || cb == 0 { flag := false; }
  if ca != cc && cb != cc { flag := false; }
  output := if flag then "YES" else "NO";
}
