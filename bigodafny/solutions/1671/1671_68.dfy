// 166_A. Rank List  (problem 1671, solution 1671_68)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # Description of the problem can be found at http://codeforces.com/problemset/problem/166/A
// 
// n, k = map(int, input().split())
// 
// l_t = list([list(map(int, input().split())) for _ in range(n)])
// l_t.sort(key=lambda x: (-x[0], x[1]))
// 
// l = 0
// h = 0
// t = 0
// 
// while k - l - 1 >= 0 and l_t[k - l - 1] == l_t[k - 1]:
//     t += 1
//     l += 1
// while k + h < n and l_t[k + h] == l_t[k - 1]:
//     t += 1
//     h += 1
// 
// print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ToPairs1671b(edges: seq<seq<int>>): seq<(int, int)>
  decreases |edges|
{
  if |edges| == 0 then []
  else [(edges[0][0], edges[0][1])] + ToPairs1671b(edges[1..])
}

function CountPair1671b(xs: seq<(int, int)>, t: (int, int)): int
  decreases |xs|
{
  if |xs| == 0 then 0
  else (if xs[0] == t then 1 else 0) + CountPair1671b(xs[1..], t)
}

method Solve(m: int, n: int, edges: seq<seq<int>>) returns (output: string)
{
  var pairs := ToPairs1671b(edges);
  var desc := Sort(pairs, (x: (int, int), y: (int, int)) => x.0 > y.0 || (x.0 == y.0 && x.1 < y.1));
  var target := desc[n - 1];
  var cnt := CountPair1671b(pairs, target);
  output := IntToString(cnt);
}
