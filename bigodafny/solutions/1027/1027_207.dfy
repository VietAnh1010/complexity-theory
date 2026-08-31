// 514_B. Han Solo and Lazer Gun  (problem 1027, solution 1027_207)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x,y = map(int, input().split())
// a = []
// for i in range(n):
//     x1, y1, = map(int, input().split())
//     a.append((x1,y1))
// d = set()
// for p, q in a:
//     x2, y2 = p-x, q-y
//     found = False
//     for x1, y1 in d:
//         if x1*y2 == x2*y1:
//             found = True
//             break
//     if not found:
//         d.add((x2,y2))
// print(len(d))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<(int, int)>) returns (output: string)
{
  var dxs: seq<int> := [];
  var dys: seq<int> := [];
  var i := 0;
  while i < |d_list|
    decreases |d_list| - i
  {
    var x2 := d_list[i].0 - b;
    var y2 := d_list[i].1 - c;
    var found := false;
    var j := 0;
    while j < |dxs|
      decreases |dxs| - j
    {
      if dxs[j] * y2 == x2 * dys[j] {
        found := true;
      }
      j := j + 1;
    }
    if !found {
      dxs := dxs + [x2];
      dys := dys + [y2];
    }
    i := i + 1;
  }
  output := IntToString(|dxs|);
}
