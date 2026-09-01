// 441_B. Valera and Fruits  (problem 2423, solution 2423_56)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, v = map(int, input().split())
// l = [0]*(3010)
// ans = 0
// for i in range(n):
//     a, b = map(int, input().split())
//     l[a] += b
// day = 1
// for i in range(3004):
//     temp = min(v, l[day-1])
//     ans += temp
//     l[day-1] -= temp
//     rem = v - temp
//     temp2 = min(rem, l[day])
//     ans+=temp2
//     l[day]-=temp2
//     day+=1
// 
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, pairs: seq<(int, int)>) returns (output: string)
{
  var l: seq<int> := [];
  var z := 0;
  while z < 3010
    decreases 3010 - z
  {
    l := l + [0];
    z := z + 1;
  }

  var idx := 0;
  while idx < n
    decreases n - idx
  {
    var a := pairs[idx].0;
    var b := pairs[idx].1;
    l := l[a := l[a] + b];
    idx := idx + 1;
  }

  var ans := 0;
  var day := 1;
  var i := 0;
  while i < 3004
    decreases 3004 - i
  {
    var temp := if k < l[day - 1] then k else l[day - 1];
    ans := ans + temp;
    l := l[day - 1 := l[day - 1] - temp];
    var rem := k - temp;
    var temp2 := if rem < l[day] then rem else l[day];
    ans := ans + temp2;
    l := l[day := l[day] - temp2];
    day := day + 1;
    i := i + 1;
  }
  output := IntToString(ans);
}
