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

method Solve(n: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 8 * |s| + 10
{
  steps := 1;
  var countOpen, s1 := CountChar661b(s, '(');
  var countClose, s2 := CountChar661b(s, ')');
  steps := steps + s1 + s2;
  if countOpen != countClose {
    output := "-1";
    steps := steps + 1;
  } else {
    var openC := 0;
    var closeC := 0;
    var count := 0;
    var i := 0;
    ghost var base1 := steps;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant steps <= base1 + 3 * i
      decreases |s| - i
    {
      if s[i] == '(' {
        openC := openC + 1;
      } else {
        closeC := closeC + 1;
        if closeC > openC { count := count + 2; }
      }
      i := i + 1;
      steps := steps + 3;
    }
    output := IntToString(count);
    steps := steps + 1;
  }
}

method CountChar661b(s: string, ch: char) returns (cnt: int, ghost steps: nat)
  ensures steps <= 2 * |s| + 1
{
  cnt := 0;
  var i := 0;
  steps := 1;
  ghost var base1 := steps;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant steps <= base1 + 2 * i
    decreases |s| - i
  {
    if s[i] == ch { cnt := cnt + 1; }
    i := i + 1;
    steps := steps + 2;
  }
}
