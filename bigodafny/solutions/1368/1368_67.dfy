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
  var t := Sort(s, (x: char, y: char) => x < y);
  var flag := true;
  if n == 0 || s[0] != 'a' { flag := false; }
  if s != t { flag := false; }
  var dic: map<char, int> := map[];
  var i := 0;
  while i < n
    decreases n - i
  {
    var c := s[i];
    var cur := if c in dic then dic[c] else 0;
    dic := dic[c := cur + 1];
    i := i + 1;
  }
  var ca := if 'a' in dic then dic['a'] else 0;
  var cb := if 'b' in dic then dic['b'] else 0;
  var cc := if 'c' in dic then dic['c'] else 0;
  if ca == 0 || cb == 0 { flag := false; }
  if ca != cc && cb != cc { flag := false; }
  output := if flag then "YES" else "NO";
}
