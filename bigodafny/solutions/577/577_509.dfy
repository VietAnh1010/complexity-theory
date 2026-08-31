// 1345_B. Card Constructions  (problem 577, solution 577_509)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// check=[2]
// i=0
// while check[-1]<=10**9:
//     check.append(check[-1]+3*i+5)
//     i+=1
// from bisect import bisect_right
// def dfs(x):
//     if x<2:
//         return 0
//     return dfs(x-check[bisect_right(check,x)-1])+1
// for _ in range(int(input())):
//     n=int(input())
//     print(dfs(n))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers_list: seq<int>) returns (output: string)
{

  var check := [2];
  var i := 0;
  while check[|check| - 1] <= 1000000000
  {
    check := check + [check[|check| - 1] + 3 * i + 5];
    i := i + 1;
  }
  var results: seq<string> := [];
  var k := 0;
  while k < |numbers_list|
  {
    results := results + [IntToString(Dfs(check, numbers_list[k]))];
    k := k + 1;
  }
  output := Join(results, "\n");
}


function FindIdxFrom(check: seq<int>, x: int, i: int, best: int): int
  requires 0 <= i <= |check|
{
  if i >= |check| then best
  else if check[i] <= x then FindIdxFrom(check, x, i + 1, i)
  else FindIdxFrom(check, x, i + 1, best)
}

function Dfs(check: seq<int>, x: int): int
  requires |check| > 0
{
  if x < 2 then 0
  else 1 + Dfs(check, x - check[FindIdxFrom(check, x, 0, 0)])
}
