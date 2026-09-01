// 9_C. Hexadecimal's Numbers  (problem 2381, solution 2381_176)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,ans=int(input()),1
// while int(bin(ans)[2:])<=n:
//     ans+=1
// print(ans-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function BinAsDecimal(x: int): int
  decreases if x < 0 then 0 else x
{
  if x <= 0 then 0
  else BinAsDecimal(x / 2) * 10 + x % 2
}

method Solve(n: int) returns (output: string)
  decreases *
{
  var ans := 1;
  while BinAsDecimal(ans) <= n
    decreases *
  {
    ans := ans + 1;
  }
  output := IntToString(ans - 1);
}
