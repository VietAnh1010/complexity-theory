// 1199_A. City Day  (problem 1820, solution 1820_180)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n , x , y = map(int,input().split())
// arr = list(map(int,input().split()))
// 
// for i in range(n):
//     if i >= x :
//         if arr[i] == min(arr[i - x : i + y + 1]):
//             print(i + 1 )
//             break
//     else:
//         if arr[i] == min(arr[0 : i + y +1]):
//             print(i + 1 )
//             break
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, c: int, d_list: seq<int>) returns (output: string)
{
  var n := a;
  var x := b;
  var y := c;
  var arr := d_list;
  var i := 0;
  var found := false;
  var result := 0;
  while i < n && !found
    decreases !found, n - i
  {
    var lo := if i >= x then i - x else 0;
    var hi := i + y + 1;
    if hi > |arr| { hi := |arr|; }
    var m := MinSeq(arr[lo..hi]);
    if arr[i] == m {
      result := i + 1;
      found := true;
    } else {
      i := i + 1;
    }
  }
  if found {
    output := IntToString(result);
  } else {
    output := "";
  }
}
