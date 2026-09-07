// 1342_B. Binary Period  (problem 662, solution 662_559)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def fun(s):
//   if s.strip("0") == "" or s.strip("1") == "":
//     return s
//  
//   ans = ""
//   n = len(s)
//  
//   for i in range(0, n):
//     if s[0] == "0":
//         ans = ans + "01"
//     else:
//         ans = ans + "10"
//     
//   
//   return ans
//  
// tc = int(input())
//  
// while tc > 0:
//    s = str(input())
//    print(fun(s))
//    tc = tc - 1
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, binary_strings: seq<string>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < n && i < |binary_strings|
    invariant 0 <= i
    decreases n - i
  {
    var s := binary_strings[i];
    if IsAllChar(s, '0') || IsAllChar(s, '1') {
      parts := parts + [s + "\n"];
    } else {
      var nn := |s|;
      if s[0] == '0' {
        parts := parts + [Repeat("01", nn) + "\n"];
      } else {
        parts := parts + [Repeat("10", nn) + "\n"];
      }
    }
    i := i + 1;
  }
  output := Join(parts, "");
}

function IsAllChar(s: string, c: char): bool
  decreases |s|
{
  if |s| == 0 then true
  else s[0] == c && IsAllChar(s[1..], c)
}
