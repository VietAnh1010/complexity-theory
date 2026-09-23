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

method Solve(n: int, a_list: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 3 * |a_list| * |a_list| + 3 * |a_list| + 5
{
  steps := 1;
  var mx := 0;
  var i := 0;
  while i < |a_list|
    invariant 0 <= i <= |a_list|
    invariant steps <= 3 * i * |a_list| + 3 * i + 2
    decreases |a_list| - i
  {
    var cnt := 0;
    var j := 0;
    while j < |a_list|
      invariant 0 <= j <= |a_list|
      invariant steps <= 3 * i * |a_list| + 3 * i + 2 + 3 * j
      decreases |a_list| - j
    {
      if a_list[j] == a_list[i] { cnt := cnt + 1; }
      j := j + 1;
      steps := steps + 3;
    }
    if cnt > mx { mx := cnt; }
    i := i + 1;
    steps := steps + 3;
  }
  var limit := if n % 2 == 1 then (n / 2) + 1 else n / 2;
  if mx > limit {
    output := "NO";
  } else {
    output := "YES";
  }
  steps := steps + 2;
}
