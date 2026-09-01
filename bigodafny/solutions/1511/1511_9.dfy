// 385_B. Bear and Strings  (problem 1511, solution 1511_9)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// if len(s) < 4: print(0)
// else:
//     a=0
//     for i in range(len(s)):
//         d=s.find("bear", i)
//         if d>=0: a+=len(s)-d-3
//     print(a)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(string_: string) returns (output: string)
{
  var s := string_;
  var n := |s|;
  if n < 4 {
    output := "0";
  } else {
    var a := 0;
    var i := 0;
    while i < n
      decreases n - i
    {
      var d := -1;
      var j := i;
      while j <= n - 4 && d == -1
        decreases n - 4 - j
      {
        if s[j..j+4] == "bear" { d := j; }
        j := j + 1;
      }
      if d >= 0 {
        a := a + (n - d - 3);
      }
      i := i + 1;
    }
    output := IntToString(a);
  }
}
