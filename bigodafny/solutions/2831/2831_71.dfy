// 769_B. News About Credit  (problem 2831, solution 2831_71)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import itertools
// 
// n = int(input())
// a = list(map(int, input().split()))
// a = [(a[0], 1)] + sorted(zip(a[1:], itertools.count(2)), reverse=True)
// w = 1
// ans = [ ]
// for r, cur in enumerate(a):
//     if r == w:
//         print(-1)
//         break
//     while w != n and cur[0] > 0:
//         ans.append("%s %s" % (cur[1], a[w][1]))
//         cur = (cur[0] - 1, cur[1])
//         w += 1
// else:
//     print(len(ans))
//     print('\n'.join(ans))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == n
  requires n >= 1
{
  var pairs: seq<(int,int)> := [];
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |pairs| == i - 1
    decreases n - i
  {
    pairs := pairs + [(a_list[i], i + 1)];
    i := i + 1;
  }
  var sorted := Sort(pairs, (x: (int,int), y: (int,int)) => x.0 > y.0 || (x.0 == y.0 && x.1 > y.1));
  var a := [(a_list[0], 1)] + sorted;
  var w := 1;
  var ans: seq<string> := [];
  var r := 0;
  var broke := false;
  while r < n && !broke
    invariant 0 <= r <= n
    invariant 0 <= w <= n
    invariant |a| == n
    decreases n - r, if broke then 0 else 1
  {
    var cur := a[r];
    if r == w {
      broke := true;
    } else {
      while w != n && cur.0 > 0
        invariant 0 <= w <= n
        decreases n - w
      {
        ans := ans + [IntToString(cur.1) + " " + IntToString(a[w].1)];
        cur := (cur.0 - 1, cur.1);
        w := w + 1;
      }
      r := r + 1;
    }
  }
  if broke {
    output := "-1\n";
  } else {
    output := IntToString(|ans|) + "\n" + Join(ans, "\n") + "\n";
  }
}
