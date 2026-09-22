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

// The two loops over literal constants (3010, 3004) are O(1): fixed in the
// source, not parameters of the input. Only the pairs loop scales with n.
method Solve(n: int, k: int, pairs: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires n <= |pairs|
  requires n >= 0
  requires forall t :: 0 <= t < |pairs| ==> 0 <= pairs[t].0 < 3010
  ensures steps <= 2 * n + 28000
{
  var l: seq<int> := [];
  var z := 0;
  steps := 1;
  while z < 3010
    invariant 0 <= z <= 3010
    invariant |l| == z
    invariant steps == 1 + z
    decreases 3010 - z
  {
    l := l + [0];
    z := z + 1;
    steps := steps + 1;
  }

  var idx := 0;
  ghost var base1 := steps;
  while idx < n
    invariant 0 <= idx <= n
    invariant |l| == 3010
    invariant steps == base1 + 2 * idx
    decreases n - idx
  {
    var a := pairs[idx].0;
    var b := pairs[idx].1;
    l := l[a := l[a] + b];
    idx := idx + 1;
    steps := steps + 2;
  }

  var ans := 0;
  var day := 1;
  var i := 0;
  ghost var base2 := steps;
  while i < 3004
    invariant 0 <= i <= 3004
    invariant day == i + 1
    invariant |l| == 3010
    invariant steps == base2 + 8 * i
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
    steps := steps + 8;
  }
  output := IntToString(ans);
  steps := steps + 1;
}
