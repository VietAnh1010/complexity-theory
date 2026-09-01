// 839_B. Game of the Rows  (problem 2426, solution 2426_4)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// seat = {4:n, 2:n*2, 1:0}
// extra1 = 0
// a = sorted(map(int, input().split()), reverse=True)
// 
// def sit(n, m):
//     num = min(seat[n], m)
//     seat[n] -= num
//     return m - num
// 
// for m in a:
//     p4 = m // 4
//     p3, p2, p1 = 0, 0, 0
//     if m%4 == 3:
//         p3 = 1
//     else:
//         p2 = int(m % 4 > 1)
//         p1 = int(m % 2)
// 
//     extra4 = sit(4, p4)
//     p2 += extra4*2
//     if sit(4, p3) > 0:
//         p2 += 1
//         p1 += 1
// 
//     extra2 = sit(2, p2)
//     x = sit(4, extra2)
//     seat[1] += extra2 - x
//     p1 += x * 2
// 
//     extra1 += p1
// 
// extra1 = sit(1, extra1)
// x = sit(4, extra1)
// seat[2] += extra1 - x
// y = sit(2, x)
// 
// if y > 0:
//     print("NO")
// else:
//     print("YES")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function Sit(cap: int, req: int): (int, int)
{
  var num := if cap < req then cap else req;
  (cap - num, req - num)
}

method Solve(n: int, m: int, values: seq<int>) returns (output: string)
{
  var sortedVals := Sort(values, (x: int, y: int) => x > y);
  var seat4 := n;
  var seat2 := n * 2;
  var seat1 := 0;
  var extra1sum := 0;
  var idx := 0;
  while idx < |sortedVals|
    decreases |sortedVals| - idx
  {
    var mm := sortedVals[idx];
    var p4 := FloorDiv(mm, 4);
    var p3 := 0;
    var p2 := 0;
    var p1 := 0;
    if FloorMod(mm, 4) == 3 {
      p3 := 1;
    } else {
      p2 := if FloorMod(mm, 4) > 1 then 1 else 0;
      p1 := FloorMod(mm, 2);
    }

    var r1 := Sit(seat4, p4);
    seat4 := r1.0;
    var extra4 := r1.1;
    p2 := p2 + extra4 * 2;

    var r2 := Sit(seat4, p3);
    seat4 := r2.0;
    var sitres3 := r2.1;
    if sitres3 > 0 {
      p2 := p2 + 1;
      p1 := p1 + 1;
    }

    var r3 := Sit(seat2, p2);
    seat2 := r3.0;
    var extra2 := r3.1;

    var r4res := Sit(seat4, extra2);
    seat4 := r4res.0;
    var x := r4res.1;
    seat1 := seat1 + (extra2 - x);
    p1 := p1 + x * 2;

    extra1sum := extra1sum + p1;
    idx := idx + 1;
  }

  var f1 := Sit(seat1, extra1sum);
  seat1 := f1.0;
  var e1 := f1.1;
  var f2 := Sit(seat4, e1);
  seat4 := f2.0;
  var x2 := f2.1;
  seat2 := seat2 + (e1 - x2);
  var f3 := Sit(seat2, x2);
  seat2 := f3.0;
  var y := f3.1;

  output := if y > 0 then "NO" else "YES";
}
