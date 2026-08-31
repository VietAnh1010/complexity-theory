// 1323_C. Unusual Competitions  (problem 661, solution 661_99)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// brak=[i for i in input()]
// open_=0
// close_=0
// if brak.count('(')!=brak.count(')'):
//     print(-1)
// else:
//     count=0
//     for i in brak:
//         if i=="(":
//             open_+=1
//         else:
//             close_+=1
//             if close_>open_:
//                count+=2
//     print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  var countOpen := CountChar661b(s, '(');
  var countClose := CountChar661b(s, ')');
  if countOpen != countClose {
    output := "-1";
  } else {
    var openC := 0;
    var closeC := 0;
    var count := 0;
    var i := 0;
    while i < |s|
      decreases |s| - i
    {
      if s[i] == '(' {
        openC := openC + 1;
      } else {
        closeC := closeC + 1;
        if closeC > openC { count := count + 2; }
      }
      i := i + 1;
    }
    output := IntToString(count);
  }
}

method CountChar661b(s: string, ch: char) returns (cnt: int)
{
  cnt := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] == ch { cnt := cnt + 1; }
    i := i + 1;
  }
}
