// 296_A. Yaroslav and Permutations  (problem 2266, solution 2266_172)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// mx = 0
// for i in a: mx = max(mx, a.count(i))
// if n%2==1:
//     if mx>(n//2)+1: print('NO')
//     else: print('YES')
// else:
//     if mx>n//2: print('NO')
//     else: print('YES')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  var mx := 0;
  var i := 0;
  while i < |a_list|
    decreases |a_list| - i
  {
    var cnt := 0;
    var j := 0;
    while j < |a_list|
      decreases |a_list| - j
    {
      if a_list[j] == a_list[i] { cnt := cnt + 1; }
      j := j + 1;
    }
    if cnt > mx { mx := cnt; }
    i := i + 1;
  }
  var limit := if n % 2 == 1 then (n / 2) + 1 else n / 2;
  if mx > limit {
    output := "NO";
  } else {
    output := "YES";
  }
}
