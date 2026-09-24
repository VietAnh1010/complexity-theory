// p02927 Japanese Student Championship 2019 Qualification - Takahashi Calendar  (problem 1954, solution 1954_83)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// M,D=map(int,input().split())
// cnt=0
// for i in range(1,M+1):
//     for j in range(1,D+1):
//         iti=j%10
//         ju=j//10
//         if iti>=2 and ju>=2 and i==iti*ju:
//             cnt+=1
//
// print(cnt)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  requires a >= 0 && b >= 0
  ensures steps <= 4 * a * b + 3
{
  steps := 1;
  var cnt := 0;
  var i := 1;
  while i <= a
    invariant 1 <= i <= a + 1
    invariant steps == 1 + 4 * b * (i - 1)
    decreases a - i + 1
  {
    var j := 1;
    while j <= b
      invariant 1 <= j <= b + 1
      invariant steps == 1 + 4 * b * (i - 1) + 4 * (j - 1)
      decreases b - j + 1
    {
      var iti := j % 10;
      var ju := j / 10;
      if iti >= 2 && ju >= 2 && i == iti * ju {
        cnt := cnt + 1;
      }
      j := j + 1;
      steps := steps + 4;
    }
    i := i + 1;
  }
  output := IntToString(cnt);
  steps := steps + 2;
}
