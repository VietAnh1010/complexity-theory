// 887_B. Cubes for Masha  (problem 1722, solution 1722_4)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def gen(cur, used, x):
//     pos.add(cur)
//     if x == n:
//         return
//     for j in range(n):
//         if not used[j]:
//             for i in a[j]:
//                 if i != 0 or x != 0:
//                     used[j] = True
//                     gen(cur * 10 + i, used, x + 1)
//                     used[j] = False
// 
// 
// n = int(input())
// a = []
// for i in range(n):
//     a.append(list(map(int, input().split())))
// pos = set()
// gen(0, [False] * n, 0)
// x = 1
// while x in pos:
//     x += 1
// print(x - 1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, lists: seq<seq<int>>) returns (output: string)
{
  var used := seq(n, (idx: int) => false);
  var pos := Gen1722_4(n, lists, 0, used, 0, {});
  var x := 1;
  while x in pos
    decreases if x in pos then 1000000 - x else 0
  {
    x := x + 1;
  }
  output := IntToString(x - 1);
}

method Gen1722_4(n: int, a: seq<seq<int>>, cur: int, used: seq<bool>, x: int, posIn: set<int>) returns (posOut: set<int>)
  decreases n - x
{
  var pos := posIn + {cur};
  if x == n {
    posOut := pos;
    return;
  }
  var j := 0;
  while j < n
    decreases n - j
  {
    if !used[j] {
      var k := 0;
      while k < |a[j]|
        decreases |a[j]| - k
      {
        var i := a[j][k];
        if i != 0 || x != 0 {
          var used2 := used[j := true];
          pos := Gen1722_4(n, a, cur * 10 + i, used2, x + 1, pos);
        }
        k := k + 1;
      }
    }
    j := j + 1;
  }
  posOut := pos;
}
