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

method Solve(a: int, b: int) returns (output: string)
{
  var cnt := 0;
  var i := 1;
  while i <= a
    decreases a - i + 1
  {
    var j := 1;
    while j <= b
      decreases b - j + 1
    {
      var iti := j % 10;
      var ju := j / 10;
      if iti >= 2 && ju >= 2 && i == iti * ju {
        cnt := cnt + 1;
      }
      j := j + 1;
    }
    i := i + 1;
  }
  output := IntToString(cnt);
}
