// 1005_C. Summarize to the Power of Two  (problem 788, solution 788_76)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l = [int(x) for x in input().split()]
// l.sort()
// if n == 0:
//     print (0)
// elif n == 1:
//     print(1)
// else:
//     Dict = {}
//     for x in l:
//         try:
//             Dict[x] += 1
//         except KeyError:
//             Dict[x] = 1
//     cnt, book =0, {}
//     for x in l:
//         if book.__contains__(x) :
//             continue
//         flag = False
//         t = 1 << 30
//         while t >= 1:
//             if  t <= x:
//                 break
//             if 2 * x == t and Dict[x] == 1:
//                 t >>= 1
//                 continue
//             if Dict.__contains__(t - x):
//                 flag , book[x], book[t-x] = True, True, True
//                 break
//             t >>= 1
//         if not flag:
//             cnt += 1
//     print(cnt)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  var l := SortInts(a_list);
  var freq: map<int,int> := map[];
  var i := 0;
  while i < |l|
    decreases |l| - i
  {
    var v := l[i];
    if v in freq { freq := freq[v := freq[v]+1]; } else { freq := freq[v := 1]; }
    i := i + 1;
  }
  if n == 0 {
    output := "0";
  } else if n == 1 {
    output := "1";
  } else {
    var book: set<int> := {};
    var cnt := 0;
    i := 0;
    while i < |l|
      decreases |l| - i
    {
      var x := l[i];
      if x !in book {
        var flag := false;
        var t := 1073741824;
        while t >= 1 && !flag
          decreases !flag, t
        {
          if t <= x {
            t := 0;
          } else if 2*x == t && x in freq && freq[x] == 1 {
            t := t / 2;
          } else if (t - x) in freq {
            flag := true;
            book := book + {x} + {t - x};
          } else {
            t := t / 2;
          }
        }
        if !flag {
          cnt := cnt + 1;
        }
      }
      i := i + 1;
    }
    output := IntToString(cnt);
  }
}
