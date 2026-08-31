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
  output := ""; // TODO: translate the Python above
}
