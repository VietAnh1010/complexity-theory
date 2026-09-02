// 299_A. Ksusha and Array  (problem 3018, solution 3018_50)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// a = int(input())
// s = [int(x) for x in input().split()]
// key = True
// c = min(s)
// for i in s:
//   if i % c != 0:
//     key = False
//     print(-1)
//     break
// if key:
//   print(c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  if |a_list| == 0 {
    output := "";
    return;
  }
  var c := MinSeq(a_list);
  var key := true;
  var result := "";
  var i := 0;
  while i < |a_list| && key
    invariant 0 <= i <= |a_list|
    decreases |a_list| - i
  {
    if c != 0 && FloorMod(a_list[i], c) != 0 {
      key := false;
      result := "-1";
    }
    i := i + 1;
  }
  if key {
    result := IntToString(c);
  }
  output := result;
}
