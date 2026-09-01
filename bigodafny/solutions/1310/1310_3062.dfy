// 116_A. Tram  (problem 1310, solution 1310_3062)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
// x = list(map(int, input().split()))
// s = []
// for i in range(0,x[0]):
//     s.append(list(map(int, input().split())))
// q = 1
// p = 0
// q = 0
// for i in range(0,x[0]):
//     p = p - s[i][0] + s[i][1]
//     if p > q :
//         q = p
// print(q)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, edges: seq<seq<int>>) returns (output: string)
{
{

  var people := 0;
  var maxPeople := 0;
  var i := 0;
  while i < n
    decreases n - i
  {
    var aa := edges[i][0];
    var bb := edges[i][1];
    people := people + bb - aa;
    if people > maxPeople { maxPeople := people; }
    i := i + 1;
  }
  output := IntToString(maxPeople);
}
}
