// 650_A. Watchmen  (problem 1853, solution 1853_66)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from collections import Counter
// n = int(input())
// a, b = [], []
// for i in range(n):
//     ai, bi = [int(x) for x in input().split()]
//     a.append(ai)
//     b.append(bi)
// sum = 0
// for k, v in dict(Counter(a)).items():
//     if v > 1:
//        sum += v*(v-1)//2
// for k, v in dict(Counter(b)).items():
//     if v > 1:
//        sum += v*(v-1)//2
// r = [(x, y) for x, y in zip(a, b)]
// for k, v in dict(Counter(r)).items():
//     if v > 1:
//        sum -= v*(v-1)//2
// print(sum)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method PairSum1853b<T(==)>(cnt: map<T, int>) returns (s: int, ghost steps: nat)
  ensures steps <= 10 * |cnt| + 3
{
  steps := 1;
  s := 0;
  var ks := cnt.Keys;
  steps := steps + |cnt|;
  while ks != {}
    invariant ks <= cnt.Keys
    invariant |ks| <= |cnt|
    invariant steps == 1 + |cnt| + 10 * (|cnt| - |ks|)
    decreases |ks|
  {
    var k :| k in ks;
    var v := cnt[k];
    if v > 1 {
      s := s + v * (v - 1) / 2;
    }
    ks := ks - {k};
    steps := steps + 10;
  }
  steps := steps + 1;
}

method Solve(n: int, coordinates: seq<(int, int)>) returns (output: string, ghost steps: nat)
  requires |coordinates| == n
  ensures steps <= 60 * n + 20 + |output|
{
  steps := 1;
  var ca: map<int, int> := map[];
  var cb: map<int, int> := map[];
  var cr: map<(int, int), int> := map[];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |ca| <= i && |cb| <= i && |cr| <= i
    invariant steps == 1 + 25 * i
    decreases n - i
  {
    var x := coordinates[i].0;
    var y := coordinates[i].1;
    ca := ca[x := (if x in ca then ca[x] else 0) + 1];
    cb := cb[y := (if y in cb then cb[y] else 0) + 1];
    cr := cr[(x, y) := (if (x, y) in cr then cr[(x, y)] else 0) + 1];
    i := i + 1;
    steps := steps + 25;
  }
  var sa, st1 := PairSum1853b(ca);
  var sb, st2 := PairSum1853b(cb);
  var sr, st3 := PairSum1853b(cr);
  steps := steps + st1 + st2 + st3;
  var total := sa + sb - sr;
  steps := steps + 3;
  output := IntToString(total);
  IntToStringDigits(total);
  steps := steps + Digits(total);
}
