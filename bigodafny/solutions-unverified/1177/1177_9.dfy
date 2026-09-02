// 785_B. Anton and Classes  (problem 1177, solution 1177_9)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// c=[]
// for i in range(n):
//     c.append(list(map(int,input().split())))
// m=int(input())
// p=[]
// for i in range(m):
//     p.append(list(map(int,input().split())))
// c.sort()
// p.sort()
// ans=0
// for i in range(n):
//     ans=max(ans,p[-1][0]-c[i][1])
// for i in range(m):
//     ans=max(ans,c[-1][0]-p[i][1])
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, rectangles: seq<(int, int)>, m: int, checks: seq<(int, int)>) returns (output: string)
{
  var c := Sort(rectangles, (p: (int,int), q: (int,int)) => p.0 < q.0 || (p.0 == q.0 && p.1 < q.1));
  var p := Sort(checks, (a: (int,int), b: (int,int)) => a.0 < b.0 || (a.0 == b.0 && a.1 < b.1));
  var ans := 0;
  var i := 0;
  while i < n
    decreases n - i
  {
    var cand := p[m-1].0 - c[i].1;
    if cand > ans { ans := cand; }
    i := i + 1;
  }
  i := 0;
  while i < m
    decreases m - i
  {
    var cand := c[n-1].0 - p[i].1;
    if cand > ans { ans := cand; }
    i := i + 1;
  }
  output := IntToString(ans);
}
