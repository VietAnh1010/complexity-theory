// 1023_C. Bracket Subsequence  (problem 1935, solution 1935_157)
// time complexity: O(1)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=map(int,input().split())
// ans=(n-k)//2
// s=input()
// s=s.replace("(","",ans)
// s=s.replace(")","",ans)
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, s: string) returns (output: string)
{
  var ans := FloorDiv(n - m, 2);
  var effAns := if ans < 0 then |s| else ans;
  var openRemoved := 0;
  var closeRemoved := 0;
  var res := "";
  var i := 0;
  while i < |s|
  {
    if s[i] == '(' && openRemoved < effAns {
      openRemoved := openRemoved + 1;
    } else if s[i] == ')' && closeRemoved < effAns {
      closeRemoved := closeRemoved + 1;
    } else {
      res := res + [s[i]];
    }
    i := i + 1;
  }
  output := res + "\n";
}
