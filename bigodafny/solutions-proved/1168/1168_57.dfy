include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string, ghost steps: nat)
  requires n == |s|
  ensures steps <= 12 * n + 6 + |output|
{
  steps := 2;
  if |s| % 2 == 1 {
    output := "-1";
  } else {
    var diff := 0;
    var ans := 0;
    var f := 'p';
    var i := 0;
    steps := steps + 1;
    while i < n
      invariant 0 <= i <= n
      invariant steps <= 12 * i + 3
      invariant 0 <= ans <= 2 * i
      decreases n - i
    {
      if s[i] == '(' {
        diff := diff + 1;
      } else if s[i] == ')' {
        diff := diff - 1;
      }
      if diff >= 0 {
        f := 'p';
      } else {
        ans := ans + 1;
        if f == 'p' {
          f := 'n';
          ans := ans + 1;
        }
      }
      i := i + 1;
      steps := steps + 12;
    }
    steps := steps + 1;
    if diff == 0 {
      output := IntToString(ans);
      IntToStringDigits(ans);
      steps := steps + Digits(ans);
    } else {
      output := "-1";
    }
  }
}
