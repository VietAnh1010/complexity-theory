// 1365_C. Rotation Matching  (problem 2188, solution 2188_371)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// a=list(map(int,input().split()))
// b=list(map(int,input().split()))
// ga={}
// gb={}
// for i in range(n):ga[a[i]]=i;gb[b[i]]=i
// g={}
// for i in range(1,n+1):o=(gb[i]-ga[i])%n;g[o]=g[o]+1if g.get(o)else 1
// print(max(g[i]for i in g))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>, b_list: seq<int>) returns (output: string)
{
  var ga := seq(n + 1, _ => 0);
  var gb := seq(n + 1, _ => 0);
  var i := 0;
  while i < n
    decreases n - i
  {
    ga := ga[a_list[i] := i];
    gb := gb[b_list[i] := i];
    i := i + 1;
  }
  var counts := seq(if n >= 0 then n else 0, _ => 0);
  i := 1;
  while i <= n
    decreases n - i + 1
  {
    var o := FloorMod(gb[i] - ga[i], n);
    counts := counts[o := counts[o] + 1];
    i := i + 1;
  }
  output := IntToString(MaxSeq(counts));
}
