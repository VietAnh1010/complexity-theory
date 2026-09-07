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
