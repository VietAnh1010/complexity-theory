// 650_A. Watchmen  (problem 1853, solution 1853_137)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = []
// b = {}
// c = {}
// for i in range(n):
//     x, y = [int(d) for d in input().split()]
//     b[y] = 0
//     a.append((x, y))
// a.sort()
// b[a[0][1]] = 1
// c[a[0][1]] = 1
// summa = 0
// count = 1
// for i in range(1, n):
//     if a[i][0] == a[i - 1][0]:
//         summa += count
//         count += 1
//     else:
//         count = 1
//         c = {}
//     b[a[i][1]] += 1
//     if a[i][1] not in c:
//         c[a[i][1]] = 0
//     c[a[i][1]] += 1
//     summa = summa + b[a[i][1]] - c[a[i][1]]
// print(summa)
//         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires |coordinates| == n
  ensures steps <= 2 * NLogN(n) + 30 * n + 12 + |output|
{
  steps := 1;
  var b: map<int, int> := map[];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant steps <= 1 + 6 * i
    invariant forall k :: 0 <= k < i ==> coordinates[k].1 in b
    decreases n - i
  {
    b := b[coordinates[i].1 := 0];
    i := i + 1;
    steps := steps + 6;
  }
  var less := (p: (int, int), q: (int, int)) => p.0 < q.0 || (p.0 == q.0 && p.1 < q.1);
  var a := Sort(coordinates, less);
  steps := steps + SortCost(n) + 2;
  SortCostWithin(n, n);
  SortKeepsElems(coordinates, less);
  assert forall x :: x in a ==> x.1 in b;
  var summa := 0;
  if n > 0 {
    steps := steps + 4;
    b := b[a[0].1 := 1];
    var c: map<int, int> := map[a[0].1 := 1];
    var count := 1;
    i := 1;
    while i < n
      invariant 1 <= i <= n
    invariant steps <= 6 * n + 1 + SortCost(n) + 2 + 4 + 24 * i
      invariant forall x :: x in a ==> x.1 in b
      decreases n - i
    {
      if a[i].0 == a[i - 1].0 {
        summa := summa + count;
        count := count + 1;
      } else {
        count := 1;
        c := map[];
      }
      b := b[a[i].1 := b[a[i].1] + 1];
      if a[i].1 !in c {
        c := c[a[i].1 := 0];
      }
      c := c[a[i].1 := c[a[i].1] + 1];
      summa := summa + b[a[i].1] - c[a[i].1];
      i := i + 1;
      steps := steps + 24;
    }
  }
  output := IntToString(summa);
  IntToStringDigits(summa);
  steps := steps + Digits(summa);
}
