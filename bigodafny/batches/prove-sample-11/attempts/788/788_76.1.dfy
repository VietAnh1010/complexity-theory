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

ghost function Log2(x: nat): nat  decreases x
{ if x <= 1 then 0 else 1 + Log2(x / 2) }

lemma Log2Big()
  ensures Log2(1073741824) == 30
{
  assert Log2(1) == 0;
  assert Log2(2) == 1;
  assert Log2(4) == 2;
  assert Log2(8) == 3;
  assert Log2(16) == 4;
  assert Log2(32) == 5;
  assert Log2(64) == 6;
  assert Log2(128) == 7;
  assert Log2(256) == 8;
  assert Log2(512) == 9;
  assert Log2(1024) == 10;
  assert Log2(1048576) == 20;
  assert Log2(1073741824) == 30;
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|a_list|) + 300 * |a_list| + |output| + 10
{
  steps := 1 + SortCost(|a_list|);
  SortCostWithin(|a_list|, |a_list|);
  var l := SortInts(a_list);
  var freq: map<int,int> := map[];
  var i := 0;
  while i < |l|
    invariant 0 <= i <= |l|
    invariant steps <= SortCost(|a_list|) + 1 + 6 * i
    decreases |l| - i
  {
    steps := steps + 6;
    var v := l[i];
    if v in freq { freq := freq[v := freq[v]+1]; } else { freq := freq[v := 1]; }
    i := i + 1;
  }
  if n == 0 {
    output := "0";
    steps := steps + 1;
  } else if n == 1 {
    output := "1";
    steps := steps + 1;
  } else {
    var book: set<int> := {};
    var cnt := 0;
    i := 0;
    ghost var s1 := steps;
    while i < |l|
      invariant 0 <= i <= |l|
      invariant steps <= s1 + 300 * i
      decreases |l| - i
    {
      steps := steps + 3;
      var x := l[i];
      if x !in book {
        var flag := false;
        var t := 1073741824;
        ghost var c := 0;
        ghost var s0 := steps;
        Log2Big();
        while t >= 1 && !flag
          invariant 0 <= t <= 1073741824
          invariant c <= 31
          invariant t >= 1 ==> c + Log2(t) <= 30
          invariant steps <= s0 + 8 * c + (if flag then 8 else 0)
          decreases !flag, t
        {
          steps := steps + 8;
          if t <= x {
            t := 0; c := c + 1;
          } else if 2*x == t && x in freq && freq[x] == 1 {
            t := t / 2; c := c + 1;
          } else if (t - x) in freq {
            flag := true;
            book := book + {x} + {t - x};
          } else {
            t := t / 2; c := c + 1;
          }
        }
        steps := steps + 2;
        if !flag {
          cnt := cnt + 1;
        }
      }
      i := i + 1;
    }
    output := IntToString(cnt);
    IntToStringDigits(cnt);
    steps := steps + Digits(cnt) + 1;
  }
}
