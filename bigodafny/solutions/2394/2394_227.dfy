// 1296_E1. String Coloring (easy version)  (problem 2394, solution 2394_227)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
//     n = int(input().strip())
//     s = input().strip()
//     result = []
//     a, b = "", ""
//     for c in s:
//         if c >= a:
//             a = c
//             result.append("1")
//         elif c >= b:
//             b = c
//             result.append("0")
//         else:
//             print("NO")
//             return
//     print("YES")
//     print("".join(result))
// 
// 
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, string_: string) returns (output: string)
{
  var s := string_;
  var m := |s|;
  var result := new char[m];
  var haveA := false;
  var aChar := 'a';
  var haveB := false;
  var bChar := 'a';
  var i := 0;
  var ok := true;
  while i < m && ok
    invariant 0 <= i <= m
  {
    var c := s[i];
    if !haveA || c >= aChar {
      aChar := c;
      haveA := true;
      result[i] := '1';
    } else if !haveB || c >= bChar {
      bChar := c;
      haveB := true;
      result[i] := '0';
    } else {
      ok := false;
    }
    i := i + 1;
  }
  if ok {
    output := "YES\n" + result[..] + "\n";
  } else {
    output := "NO\n";
  }
}
