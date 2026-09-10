// 2381_176 (problem 2381) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(1)
//   proved bound    : 20000000000
//   proved class    : O(1)
//   agent verdict   : gave_up
//   reference label : O(n)
//   prediction correct against the label: False
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     single scalar input n; loop trip count depends on n's value (count of
//     0/1-digit decimals <= n), and description.md caps n <= 10^9, so trip
//     count is bounded by a fixed constant (~1023) regardless of any growing
//     size
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 2381_176
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// n,ans=int(input()),1
// while int(bin(ans)[2:])<=n:
//     ans+=1
// print(ans-1)
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function BinAsDecimal(x: int): int
  decreases if x < 0 then 0 else x
{
  if x <= 0 then 0
  else BinAsDecimal(x / 2) * 10 + x % 2
}

// same digit pattern read in base 10 is never smaller than read in base 2
lemma BinAsDecimalGE(x: int)
  requires x >= 1
  ensures BinAsDecimal(x) >= x
  decreases x
{
  if x >= 2 {
    BinAsDecimalGE(x / 2);
    assert x / 2 * 2 <= x;
  }
}

method Solve(n: int) returns (output: string, ghost steps: nat)
  requires 1 <= n <= 1000000000
  ensures steps <= 20000000000
{
  steps := 1;
  var ans := 1;
  while BinAsDecimal(ans) <= n
    invariant 1 <= ans <= n + 1
    invariant steps <= 15 * ans + 10
    decreases n + 1 - ans
  {
    BinAsDecimalGE(ans);
    ans := ans + 1;
    steps := steps + 15;
  }
  output := IntToString(ans - 1);
  steps := steps + 1;
}
