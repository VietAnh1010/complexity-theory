// 208_D. Prizes, Prizes, more Prizes  (problem 1092, solution 1092_0)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import bisect
// 
// n = int(input())
// a = [int(x) for x in input().split()]
// p = [int(x) for x in input().split()]
// b = [0, 0, 0, 0, 0]
// s = 0
// for i in a:
//     s += i
//     k = bisect.bisect_right(p, s)
//     while k != 0:
//         if (k == 5) or (p[k] > s):
//             k -= 1
//         b[k] += s // p[k]
//         s %= p[k]
//         k = bisect.bisect_right(p, s)
// print(' '.join(list(map(str, b))))
// print(s)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  var prizes := SortInts(b_list);
  var aC := 0;
  var bC := 0;
  var cC := 0;
  var dC := 0;
  var eC := 0;
  var s := 0;
  var idx := 0;
  while idx < |a_list|
    decreases |a_list| - idx
  {
    s := s + a_list[idx];
    if s >= prizes[4] { eC := eC + FloorDiv(s, prizes[4]); s := FloorMod(s, prizes[4]); }
    if s >= prizes[3] { dC := dC + FloorDiv(s, prizes[3]); s := FloorMod(s, prizes[3]); }
    if s >= prizes[2] { cC := cC + FloorDiv(s, prizes[2]); s := FloorMod(s, prizes[2]); }
    if s >= prizes[1] { bC := bC + FloorDiv(s, prizes[1]); s := FloorMod(s, prizes[1]); }
    if s >= prizes[0] { aC := aC + FloorDiv(s, prizes[0]); s := FloorMod(s, prizes[0]); }
    idx := idx + 1;
  }
  output := Join([IntToString(aC), IntToString(bC), IntToString(cC), IntToString(dC), IntToString(eC)], " ") + "\n" + IntToString(s);
}

