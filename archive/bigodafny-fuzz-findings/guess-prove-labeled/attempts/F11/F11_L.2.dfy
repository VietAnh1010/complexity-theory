// --- Python ---------------------------------------------------------
// def settle(c):
//     n = len(c)
//     stack = [i for i in range(n) if c[i] >= 2]
//     moves = 0
//     while stack:
//         i = stack.pop()
//         c[i] -= 2
//         moves += 1
//         if i > 0:
//             c[i - 1] += 1
//             if c[i - 1] == 2:
//                 stack.append(i - 1)
//         if i + 1 < n:
//             c[i + 1] += 1
//             if c[i + 1] == 2:
//                 stack.append(i + 1)
//         if c[i] >= 2:
//             stack.append(i)
//     return moves
//
// n = int(input())
// c = list(map(int, input().split()))
// moves = settle(c)
// print(moves, sum(c))
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

ghost function W(j: int, n: int): int
{
  (j + 1) * (n - j)
}

ghost function Pot(s: seq<int>, k: nat, n: int): int
  requires k <= |s|
  decreases k
{
  if k == 0 then 0 else Pot(s, k - 1, n) + s[k - 1] * W(k - 1, n)
}

lemma MulAddDist(a: int, b: int, c: int)
  ensures (a + b) * c == a * c + b * c
{
}

lemma WSecond(i: int, n: int)
  ensures W(i - 1, n) + W(i + 1, n) - 2 * W(i, n) == -2
{
}

lemma PotUpd(s: seq<int>, t: seq<int>, k: nat, n: int, p: int, d: int)
  requires |s| == |t| && k <= |s| && 0 <= p < |s|
  requires t == s[p := s[p] + d]
  ensures Pot(t, k, n) == Pot(s, k, n) + (if p < k then d * W(p, n) else 0)
  decreases k
{
  if k > 0 {
    PotUpd(s, t, k - 1, n, p, d);
    if p == k - 1 {
      assert t[k - 1] == s[k - 1] + d;
      MulAddDist(s[k - 1], d, W(k - 1, n));
    } else {
      assert t[k - 1] == s[k - 1];
    }
  }
}

lemma PotFire(s0: seq<int>, s3: seq<int>, n: int, i: int)
  requires |s0| == n && |s3| == n && 0 <= i < n
  requires s3[i] == s0[i] - 2
  requires i > 0 ==> s3[i - 1] == s0[i - 1] + 1
  requires i + 1 < n ==> s3[i + 1] == s0[i + 1] + 1
  requires forall j :: 0 <= j < n && j != i && j != i - 1 && j != i + 1 ==> s3[j] == s0[j]
  ensures Pot(s3, n, n) == Pot(s0, n, n) - 2
{
  var t1 := s0[i := s0[i] - 2];
  PotUpd(s0, t1, n, n, i, -2);
  var t2 := if i > 0 then t1[i - 1 := t1[i - 1] + 1] else t1;
  if i > 0 {
    PotUpd(t1, t2, n, n, i - 1, 1);
  } else {
    assert W(i - 1, n) == 0;
  }
  var t3 := if i + 1 < n then t2[i + 1 := t2[i + 1] + 1] else t2;
  if i + 1 < n {
    PotUpd(t2, t3, n, n, i + 1, 1);
  } else {
    assert W(i + 1, n) == 0;
  }
  assert |t3| == n;
  assert forall j :: 0 <= j < n ==> t3[j] == s3[j];
  assert t3 == s3;
  WSecond(i, n);
}

lemma PotNonneg(s: seq<int>, k: nat, n: nat)
  requires k <= |s| && k <= n
  requires forall j :: 0 <= j < k ==> 0 <= s[j]
  ensures Pot(s, k, n) >= 0
  decreases k
{
  if k > 0 {
    PotNonneg(s, k - 1, n);
    var x: nat := s[k - 1];
    var a: nat := k;
    var b: nat := n - (k - 1);
    assert W(k - 1, n) == a * b;
    CostMulMono(a, 0, b);
    var ab: nat := a * b;
    CostMulMono(x, 0, ab);
    assert s[k - 1] * W(k - 1, n) == x * ab;
  }
}

lemma PotLe(s: seq<int>, k: nat, n: nat)
  requires k <= |s| && k <= n
  requires forall j :: 0 <= j < k ==> 0 <= s[j] <= 3
  ensures Pot(s, k, n) <= k * (3 * (n * n))
  decreases k
{
  if k > 0 {
    PotLe(s, k - 1, n);
    var x: nat := s[k - 1];
    var a: nat := k;
    var b: nat := n - (k - 1);
    assert W(k - 1, n) == a * b;
    CostMulMonoLeft(a, n, b);
    CostMulMono(n, b, n);
    var ab: nat := a * b;
    assert ab <= n * n;
    CostMulMonoLeft(x, 3, ab);
    assert s[k - 1] * W(k - 1, n) == x * ab;
    var M: nat := 3 * (n * n);
    CostMulDistrib(k - 1, 1, k, M);
    assert 1 * M == M;
  }
}

lemma Scale3(n: nat, q: nat)
  ensures n * (3 * q) == 3 * (n * q)
{
}

lemma BoundedSet(S: set<int>, n: nat)
  requires forall x :: x in S ==> 0 <= x < n
  ensures |S| <= n
  decreases n
{
  if n == 0 {
    assert S == {};
  } else {
    var S2 := S - {n - 1};
    BoundedSet(S2, n - 1);
    if (n - 1) in S {
      assert |S| == |S2| + 1;
    } else {
      assert S2 == S;
    }
  }
}

method {:isolate_assertions} Settle(c: array<int>) returns (moves: int, ghost steps: nat)
  requires forall i :: 0 <= i < c.Length ==> 0 <= c[i] <= 3
  ensures steps <= 60 * (c.Length * (c.Length * c.Length)) + 8 * c.Length + 5
  modifies c
{
  steps := 0;
  steps := steps + 1;
  var n := c.Length;
  steps := steps + (1 + (n + 1));
  var stack := new int[n + 1];
  var top := 0;
  var k := 0;
  ghost var inSet: set<int> := {};
  while k < n
    invariant 0 <= k <= n
    invariant steps <= n + 3 + 7 * k
    invariant 0 <= top <= k && top == |inSet|
    invariant forall x :: x in inSet ==> 0 <= x < k && c[x] >= 2
    invariant forall p :: 0 <= p < top ==> stack[p] in inSet
    invariant forall p, q :: 0 <= p < q < top ==> stack[p] != stack[q]
    invariant forall j :: 0 <= j < n ==> 0 <= c[j] <= 3
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 2;
    if c[k] >= 2 {
      steps := steps + 1;
      stack[top] := k;
      steps := steps + 1;
      top := top + 1;
      inSet := inSet + {k};
    }
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  moves := 0;
  BoundedSet(inSet, n);
  PotNonneg(c[..], n, n);
  PotLe(c[..], n, n);
  ghost var P0 := Pot(c[..], n, n);
  while top > 0
    invariant 0 <= top <= n && top == |inSet|
    invariant forall x :: x in inSet ==> 0 <= x < n && c[x] >= 2
    invariant forall p :: 0 <= p < top ==> stack[p] in inSet
    invariant forall p, q :: 0 <= p < q < top ==> stack[p] != stack[q]
    invariant forall j :: 0 <= j < n ==> 0 <= c[j]
    invariant moves >= 0
    invariant steps <= 8 * n + 4 + 40 * moves
    invariant Pot(c[..], n, n) + 2 * moves == P0
    invariant Pot(c[..], n, n) >= 0
    decreases Pot(c[..], n, n)
  {
    steps := steps + 2;
    steps := steps + 1;
    top := top - 1;
    steps := steps + 1;
    var i := stack[top];
    ghost var s0 := c[..];
    assert i in inSet;
    assert c[i] >= 2;
    assert forall p :: 0 <= p < top ==> stack[p] != i;
    inSet := inSet - {i};
    steps := steps + 3;
    c[i] := c[i] - 2;
    steps := steps + 1;
    moves := moves + 1;
    steps := steps + 1;
    if i > 0 {
      ghost var pre := c[i - 1];
      assert (i - 1) in inSet ==> pre >= 2;
      steps := steps + 5;
      c[i - 1] := c[i - 1] + 1;
      steps := steps + 3;
      if c[i - 1] == 2 {
        BoundedSet(inSet, n);
        assert (i - 1) !in inSet;
        steps := steps + 2;
        stack[top] := i - 1;
        steps := steps + 1;
        top := top + 1;
        inSet := inSet + {i - 1};
      }
    }
    steps := steps + 2;
    if i + 1 < n {
      ghost var pre2 := c[i + 1];
      assert (i + 1) in inSet ==> pre2 >= 2;
      steps := steps + 5;
      c[i + 1] := c[i + 1] + 1;
      steps := steps + 3;
      if c[i + 1] == 2 {
        BoundedSet(inSet, n);
        assert (i + 1) !in inSet;
        steps := steps + 2;
        stack[top] := i + 1;
        steps := steps + 1;
        top := top + 1;
        inSet := inSet + {i + 1};
      }
    }
    steps := steps + 2;
    if c[i] >= 2 {
      BoundedSet(inSet, n);
      assert i !in inSet;
      steps := steps + 1;
      stack[top] := i;
      steps := steps + 1;
      top := top + 1;
      inSet := inSet + {i};
    }
    PotFire(s0, c[..], n, i);
    PotNonneg(c[..], n, n);
  }
  steps := steps + 1;
  Scale3(n, n * n);
  assert 2 * moves <= P0;
  assert P0 <= n * (3 * (n * n));
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  ensures steps <= 60 * (n * (n * n)) + 20 * n + 10 + 2 * |output|
{
  steps := 0;
  steps := steps + n;
  var c := new int[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant steps <= n + 5 * k
    invariant forall j :: 0 <= j < k ==> c[j] == a_list[j]
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 2;
    c[k] := a_list[k];
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  var moves, s0 := Settle(c);
  steps := steps + s0;
  ghost var S0 := steps;
  var left := 0;
  k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant steps <= S0 + 5 * k
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 2;
    left := left + c[k];
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  steps := steps + (Digits(moves) + |" "| + Digits(left) + |IntToString(left)|);
  output := IntToString(moves) + " " + IntToString(left);
  IntToStringDigits(moves);
  IntToStringDigits(left);
  assert c.Length == n;
}

import opened Prelude
