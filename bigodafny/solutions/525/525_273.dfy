// 1131_B. Draw!  (problem 525, solution 525_273)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// pair = [None] * n
// 
// count = 0
// add = 0
// 
// for i in range(n):
//     pair[i] = list(map(int,input().split()))
// 
// 
// if(min(pair[0]) != 0):
//     add += min(pair[0]) + 1
// else:
//     add += 1
// 
// #print(add)
// 
// count+= add
// 
// for i in range(1,n):
//     if(min(pair[i])  - max(pair[i-1]) < 0):
//         continue
//     add = max( min(pair[i])  - max(pair[i-1]) + 1  , 0 )
//     if(pair[i-1][0] == pair[i-1][1]):
//         add -= 1
//     #print('bc',add)
//     count += add
// 
// print(count)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, points: seq<seq<int>>) returns (output: string)
{
  var p0 := points[0];
  var mn0 := if p0[0] < p0[1] then p0[0] else p0[1];
  var count := if mn0 != 0 then mn0 + 1 else 1;
  var i := 1;
  while i < n
    decreases n - i
  {
    var pi := points[i];
    var pprev := points[i-1];
    var mni := if pi[0] < pi[1] then pi[0] else pi[1];
    var mxprev := if pprev[0] > pprev[1] then pprev[0] else pprev[1];
    if mni - mxprev >= 0 {
      var a2 := mni - mxprev + 1;
      var a3 := if a2 > 0 then a2 else 0;
      if pprev[0] == pprev[1] {
        a3 := a3 - 1;
      }
      count := count + a3;
    }
    i := i + 1;
  }
  output := IntToString(count) + "\n";
}
