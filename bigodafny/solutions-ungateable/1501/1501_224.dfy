// GATE INAPPLICABLE -- `difftest.py` cannot reach a verdict on this row.
//
//   tests stored    : 122
//   comparable      : 93    (29 are python-failed: the row's own Python does
//                            not finish, so there is nothing to compare against)
//   agree           : 77
//   disagree        : 0     no test produces a different answer
//   timeout         : 16
//   recorded status : `differs`, because difftest.py requires agree ==
//                     comparable and 16 tests time out
//   re-measured     : 2026-09-21, 39 minutes, reproduced the stored record
//                     exactly -- see batches/gate-audit/difftest_1501_224.json
//   record          : data/gate_ungateable.jsonl
//   filed           : solutions-ungateable/, 2026-09-21
//
// 1177_A. Digits Sequence (Easy Edition)  (problem 1501, solution 1501_224)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// number = int(input())
// count = 0
// while number-len(str(count+1)) >= 0:
//     number-=len(str(count+1))
//     count+=1
// if number==0:
//     count = str(count)
//     print(count[-1])
// else:
//     count+=1
//     count = str(count)
//     print(count[number-1])
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
  requires n >= 1
{
  var number := n;
  var count := 0;
  while number - NumDigits(count + 1) >= 0
    invariant count >= 0
    invariant number >= 0
    decreases number
  {
    number := number - NumDigits(count + 1);
    count := count + 1;
  }
  if number == 0 {
    var s := IntToString(count);
    output := [s[|s| - 1]] + "\n";
  } else {
    var countNext := count + 1;
    var s := IntToString(countNext);
    LenIntToString(countNext);
    output := [s[number - 1]] + "\n";
  }
}

function NumDigits(k: int): int
  requires k >= 1
  ensures NumDigits(k) >= 1
  decreases k
{
  if k < 10 then 1 else 1 + NumDigits(k / 10)
}

lemma LenIntToString(x: int)
  requires x >= 1
  ensures |IntToString(x)| == NumDigits(x)
  decreases x
{
  if x < 10 {
  } else {
    LenIntToString(x / 10);
  }
}
