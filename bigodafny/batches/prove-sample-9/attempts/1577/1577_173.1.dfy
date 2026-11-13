// 1155_A. Reverse a Substring  (problem 1577, solution 1577_173)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// s=input()
// f=0
// for i in range(len(s)-1):
//     if s[i+1]<s[i]:
//         print("YES")
//         print(i+1,i+2)
//         f=1
//         break
// if f==0:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string, ghost steps: nat)
  requires n <= |s|
  ensures steps <= 6 * (if n > 0 then n else 0) + 2 * |output| + 8
{
  steps := 0;
  var i := 0;
  var found := false;
  var idx := 0;
  while i < n - 1 && !found
    invariant 0 <= i <= (if n > 0 then n else 0)
    invariant steps == 6 * i
    decreases !found, n - 1 - i
  {
    if s[i+1] < s[i] {
      found := true;
      idx := i;
      steps := steps + 6;
    } else {
      i := i + 1;
      steps := steps + 6;
    }
  }
  if found {
    output := "YES\n" + IntToString(idx + 1) + " " + IntToString(idx + 2);
    IntToStringDigits(idx + 1);
    IntToStringDigits(idx + 2);
    steps := steps + 2 * Digits(idx + 1) + 2 * Digits(idx + 2) + 5;
  } else {
    output := "NO";
    steps := steps + 3;
  }
}
