// 988_B. Substrings Sort  (problem 1272, solution 1272_278)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solve(arr):
//     for i in range(0,len(arr)-1):
//         x = arr[i+1].find(arr[i])
//        # print(x)
//         if x == -1:
//             return 0
//     return 1
// n=int(input())
// arr = []
// while n:
//     s = str(input())
//     arr.append(s)
//     n=n-1
// arr.sort(key=len)
// flag = solve(arr)
// if flag:
//     print("YES")
//     for i in arr:
//         print(i)
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsFrom1272b(hay: string, needle: string, pos: nat): bool
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  if pos + |needle| > |hay| then false
  else if hay[pos..pos+|needle|] == needle then true
  else ContainsFrom1272b(hay, needle, pos + 1)
}

function Contains1272b(hay: string, needle: string): bool
{
  |needle| == 0 || ContainsFrom1272b(hay, needle, 0)
}

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var arr := Sort(strings, (x: string, y: string) => |x| < |y|);
  var flag := true;
  var i := 0;
  while i < |arr| - 1
    decreases |arr| - 1 - i
  {
    if !Contains1272b(arr[i+1], arr[i]) { flag := false; }
    i := i + 1;
  }
  if flag {
    var lines: seq<string> := ["YES"];
    var m := 0;
    while m < |arr|
      decreases |arr| - m
    {
      lines := lines + [arr[m]];
      m := m + 1;
    }
    output := Join(lines, "\n");
  } else {
    output := "NO";
  }
}
