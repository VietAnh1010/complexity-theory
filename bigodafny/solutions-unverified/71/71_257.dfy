// 454_B. Little Pony and Sort by Shift  (problem 71, solution 71_257)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #Codeforces454B
// n = int(input())
// lst = [int(x) for x in input().split()]
// index = 0
// count = 0
// for i in range(n):
//     
//     if lst[i-1] > lst[i]:
//         index = i
//         count += 1
//     if count == 2:
//         print(-1)
//         break
// 
// if count != 2:
//     print((n - index) % n)
//  
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1 && n == |a_list|
{
  var index := 0;
  var count := 0;
  var printed := false;
  var result := "";
  var i := 0;
  while i < n && !printed
    invariant 0 <= i <= n
    decreases n - i
  {
    var prevIdx := if i == 0 then n - 1 else i - 1;
    if a_list[prevIdx] > a_list[i] {
      index := i;
      count := count + 1;
    }
    if count == 2 {
      result := "-1";
      printed := true;
    }
    i := i + 1;
  }
  if !printed {
    var r := (n - index) % n;
    result := IntToString(r);
  }
  output := result;
}
