// --- Python ---------------------------------------------------------
// n = int(input())
// a = list(map(int, input().split()))
// alive = [1] * n
// p = n - 1
// for t in range(n):
//     s = a[t] + 1
//     while s > 0:
//         p = (p + 1) % n
//         if alive[p]:
//             s -= 1
//     alive[p] = 0
// print(p + 1)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

// number of steps from p forward to reach q (1..n)
ghost function Sc(p: int, q: int, n: int): int
  requires n >= 1
{
  (q - p - 1 + n) % n + 1
}

lemma ScVal(p: int, q: int, n: int)
  requires n >= 1 && 0 <= p < n && 0 <= q < n
  ensures Sc(p, q, n) == (if q > p then q - p else q - p + n)
{
  var v := q - p - 1 + n;
  if q > p {
    ModUpper(v, n);
  } else {
    SmallMod(v, n);
  }
}

lemma ScStep(p: int, q: int, n: int)
  requires n >= 1 && 0 <= p < n && 0 <= q < n
  ensures 0 <= (p + 1) % n < n
  ensures 1 <= Sc(p, q, n) <= n
  ensures Sc(p, q, n) > 1 ==> (p + 1) % n != q && Sc((p + 1) % n, q, n) == Sc(p, q, n) - 1
  ensures Sc(p, q, n) == 1 ==> (p + 1) % n == q && Sc((p + 1) % n, q, n) == n
{
  ScVal(p, q, n);
  if p + 1 < n {
    SmallMod(p + 1, n);
    ScVal(p + 1, q, n);
  } else {
    assert p + 1 == n;
    assert (p + 1) % n == 0;
    ScVal(0, q, n);
  }
}

ghost function Lin(s: int, n: int): int
{
  s * (n + 1)
}

lemma LinStep(s: int, n: int)
  ensures Lin(s - 1, n) + n + 1 == Lin(s, n)
{
}

lemma LinMono(s: int, n: int)
  requires 0 <= s <= 4 && n >= 0
  ensures 0 <= Lin(s, n) <= 4 * n + 4
{
  if s == 0 {} else if s == 1 {} else if s == 2 {} else if s == 3 {} else {}
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  ensures steps <= n * (35 * n + 35) + 5 * n + 4 + |output|
{
  steps := 0;
  steps := steps + n;
  var alive := new int[n];
  var k := 0;
  ghost var aliveSet: set<int> := {};
  while k < n
    invariant 0 <= k <= n
    invariant alive.Length == n
    invariant forall i :: 0 <= i < k ==> alive[i] == 1
    invariant forall i :: i in aliveSet <==> 0 <= i < k
    invariant |aliveSet| == k
    invariant steps == n + 4 * k
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 1;
    alive[k] := 1;
    aliveSet := aliveSet + {k};
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  steps := steps + 1;
  var p := n - 1;
  var t := 0;
  ghost var bigK: nat := 35 * n + 35;
  while t < n
    invariant 0 <= t <= n
    invariant 0 <= p < n
    invariant alive.Length == n
    invariant forall i :: 0 <= i < n ==> (alive[i] == 1 <==> i in aliveSet)
    invariant forall i :: i in aliveSet ==> 0 <= i < n
    invariant |aliveSet| == n - t
    invariant steps <= 5 * n + 2 + t * bigK
    decreases n - t
  {
    steps := steps + 2;
    steps := steps + 2;
    var s := a_list[t] + 1;
    assert aliveSet != {};
    ghost var q :| q in aliveSet;
    ghost var steps0 := steps;
    ghost var it: nat := 0;
    LinMono(s, n);
    ScStep(p, q, n);
    while s > 0
      invariant 0 <= s <= a_list[t] + 1
      invariant 0 <= p < n
      invariant 0 <= q < n && alive[q] == 1
      invariant s < a_list[t] + 1 ==> alive[p] == 1
      invariant 1 <= Sc(p, q, n) <= n
      invariant it + Lin(s, n) + Sc(p, q, n) <= 5 * n + 4
      invariant steps <= steps0 + 7 * it
      decreases s, Sc(p, q, n)
    {
      steps := steps + 2;
      steps := steps + 2;
      ghost var oldSc := Sc(p, q, n);
      ScStep(p, q, n);
      LinStep(s, n);
      LinMono(s, n);
      p := (p + 1) % n;
      steps := steps + 2;
      if alive[p] == 1 {
        steps := steps + 1;
        s := s - 1;
      }
      it := it + 1;
      LinMono(s, n);
      ScStep(p, q, n);
    }
    steps := steps + 1;
    steps := steps + 1;
    alive[p] := 0;
    aliveSet := aliveSet - {p};
    steps := steps + 1;
    t := t + 1;
    CostMulDistrib(t - 1, 1, t, bigK);
  }
  steps := steps + 1;
  steps := steps + (1 + Digits(p + 1));
  output := IntToString(p + 1);
  IntToStringDigits(p + 1);
}

import opened Prelude
