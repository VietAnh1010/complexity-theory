// p03362 AtCoder Beginner Contest 096 - Five  Five Everywhere  (problem 1303, solution 1303_8)
// time complexity: O(n**2)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// P, A = [2], [2]
// for i in range(3, 55556, 2):
//     for p in P:
//         if i % p == 0: break
//     else:
//         P.append(i)
//         if i % 5 == 2: A.append(i)
//     if len(A) == n: break
// print(*A)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  var P: seq<int> := [2];
  var A: seq<int> := [2];
  var i := 3;
  var doneOuter := false;
  while i < 55556 && !doneOuter
    invariant forall t :: 0 <= t < |P| ==> P[t] >= 2
    decreases 55556 - i
  {
    var isPrime := true;
    var j := 0;
    while j < |P| && isPrime
      invariant 0 <= j <= |P|
      invariant forall t :: 0 <= t < |P| ==> P[t] >= 2
      decreases |P| - j
    {
      if i % P[j] == 0 {
        isPrime := false;
      }
      j := j + 1;
    }
    if isPrime {
      P := P + [i];
      if i % 5 == 2 {
        A := A + [i];
      }
    }
    if |A| == n {
      doneOuter := true;
    }
    i := i + 2;
  }
  output := JoinInts(A, " ") + "\n";
}
