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

lemma WStep(i: int, n: int)
  ensures W(i - 1, n) + W(i + 1, n) - 2 * W(i, n) == -2
{
}

lemma MulNn(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a * b >= 0
{
}

lemma MulLe(a: int, b: int, c: int, d: int)
  requires 0 <= a <= c && 0 <= b <= d
  ensures a * b <= c * d
{
  MulNn(c - a, b);
  MulNn(c, d - b);
  assert (c - a) * b == c * b - a * b;
  assert c * (d - b) == c * d - c * b;
}

lemma WBound(j: int, n: int)
  requires 0 <= j < n
  ensures 0 <= W(j, n) <= n * n
{
  MulNn(j + 1, n - j);
  MulLe(j + 1, n - j, n, n);
}

ghost function Phi(s: seq<int>, j: nat, n: int): int
  requires j <= |s|
  decreases |s| - j
{
  if j == |s| then 0 else s[j] * W(j, n) + Phi(s, j + 1, n)
}

lemma PhiUpd(s: seq<int>, t: seq<int>, i: int, d: int, j: nat, n: int)
  requires |t| == |s| && 0 <= i < |s| && j <= |s|
  requires forall k :: 0 <= k < |s| && k != i ==> t[k] == s[k]
  requires t[i] == s[i] + d
  ensures Phi(t, j, n) == Phi(s, j, n) + (if j <= i then d * W(i, n) else 0)
  decreases |s| - j
{
  if j < |s| {
    PhiUpd(s, t, i, d, j + 1, n);
    if j == i {
      assert t[j] * W(j, n) == s[j] * W(j, n) + d * W(j, n);
    } else {
      assert t[j] == s[j];
    }
  }
}

lemma PhiNonneg(s: seq<int>, j: nat, n: int)
  requires j <= |s| <= n
  requires forall k :: 0 <= k < |s| ==> s[k] >= 0
  ensures Phi(s, j, n) >= 0
  decreases |s| - j
{
  if j < |s| {
    WBound(j, n);
    MulNn(s[j], W(j, n));
    PhiNonneg(s, j + 1, n);
  }
}

lemma PhiBound(s: seq<int>, j: nat, n: int)
  requires j <= |s| <= n
  requires forall k :: 0 <= k < |s| ==> 0 <= s[k] <= 3
  ensures Phi(s, j, n) <= (|s| - j) * (3 * (n * n))
  decreases |s| - j
{
  if j < |s| {
    WBound(j, n);
    MulLe(s[j], W(j, n), 3, n * n);
    PhiBound(s, j + 1, n);
    assert (|s| - j) * (3 * (n * n)) == (|s| - j - 1) * (3 * (n * n)) + 3 * (n * n);
  }
}

ghost predicate Good(st: seq<int>, n: int)
{
  (forall p :: 0 <= p < |st| ==> 0 <= st[p] < n) &&
  (forall p, q :: 0 <= p < q < |st| ==> st[p] != st[q])
}

lemma GoodPush(st: seq<int>, x: int, n: int)
  requires Good(st, n)
  requires 0 <= x < n
  requires x !in st
  ensures Good(st + [x], n)
{
  var t := st + [x];
  forall p | 0 <= p < |t| ensures 0 <= t[p] < n {
    if p < |st| { assert t[p] == st[p]; }
  }
  forall p, q | 0 <= p < q < |t| ensures t[p] != t[q] {
    if q == |st| {
      assert t[p] == st[p];
      assert st[p] in st;
    } else {
      assert t[p] == st[p] && t[q] == st[q];
    }
  }
}

lemma GoodPrefix(st: seq<int>, n: int, k: int)
  requires Good(st, n) && 0 <= k <= |st|
  ensures Good(st[..k], n)
{
}

lemma GoodLast(st: seq<int>, n: int)
  requires Good(st, n) && |st| > 0
  ensures st[|st| - 1] !in st[..|st| - 1]
{
  var m := |st| - 1;
  if st[m] in st[..m] {
    var p :| 0 <= p < m && st[..m][p] == st[m];
    assert st[..m][p] == st[p];
    assert false;
  }
}

lemma SetBound(S: set<int>, n: int)
  requires n >= 0
  requires forall x :: x in S ==> 0 <= x < n
  ensures |S| <= n
  decreases n
{
  if n == 0 {
    assert S == {};
  } else {
    var S2 := S - {n - 1};
    SetBound(S2, n - 1);
    if n - 1 in S {
      assert S == S2 + {n - 1};
      assert S2 * {n - 1} == {};
      assert |S| == |S2| + |{n - 1}|;
    } else {
      assert S2 == S;
    }
  }
}

lemma DistinctCard(st: seq<int>)
  requires forall p, q :: 0 <= p < q < |st| ==> st[p] != st[q]
  ensures |set x | x in st| == |st|
  decreases |st|
{
  if |st| > 0 {
    var m := |st| - 1;
    var pre := st[..m];
    DistinctCard(pre);
    var last := st[m];
    if last in pre {
      var p :| 0 <= p < m && pre[p] == last;
      assert st[p] == pre[p];
      assert false;
    }
    assert (set x | x in st) == (set x | x in pre) + {last};
    assert (set x | x in pre) * {last} == {};
    assert |(set x | x in st)| == |(set x | x in pre)| + |{last}|;
  }
}

lemma GoodBound(st: seq<int>, n: int)
  requires n >= 0 && Good(st, n)
  ensures |st| <= n
{
  DistinctCard(st);
  SetBound((set x | x in st), n);
}

ghost predicate RelS(cs: seq<int>, st: seq<int>, n: int, skip: int)
{
  forall j :: 0 <= j < n && j < |cs| && j != skip ==> ((cs[j] >= 2) <==> j in st)
}

ghost predicate NN(cs: seq<int>)
{
  forall j :: 0 <= j < |cs| ==> cs[j] >= 0
}

lemma PhiAdd(s: seq<int>, i: int, d: int, n: int)
  requires 0 <= i < |s|
  ensures Phi(s[i := s[i] + d], 0, n) == Phi(s, 0, n) + d * W(i, n)
{
  PhiUpd(s, s[i := s[i] + d], i, d, 0, n);
}

lemma Pop(cs: seq<int>, st0: seq<int>, n: int)
  requires |cs| == n && NN(cs) && Good(st0, n) && RelS(cs, st0, n, -1) && |st0| > 0
  ensures Good(st0[..|st0| - 1], n)
  ensures st0[|st0| - 1] !in st0[..|st0| - 1]
  ensures 0 <= st0[|st0| - 1] < n && cs[st0[|st0| - 1]] >= 2
  ensures RelS(cs[st0[|st0| - 1] := cs[st0[|st0| - 1]] - 2], st0[..|st0| - 1], n, st0[|st0| - 1])
  ensures NN(cs[st0[|st0| - 1] := cs[st0[|st0| - 1]] - 2])
{
  GoodLast(st0, n);
  GoodPrefix(st0, n, |st0| - 1);
  var m := |st0| - 1;
  var i := st0[m];
  var st1 := st0[..m];
  assert st0 == st1 + [i];
  assert i in st0;
  var cs2 := cs[i := cs[i] - 2];
  forall j | 0 <= j < n && j != i ensures (cs2[j] >= 2) <==> j in st1 {
    assert cs2[j] == cs[j];
    assert (j in st0) <==> (j in st1);
  }
}

lemma BumpRel(cs: seq<int>, st: seq<int>, n: int, x: int, skip: int)
  requires |cs| == n && NN(cs) && Good(st, n) && RelS(cs, st, n, skip)
  requires 0 <= x < n && x != skip && skip !in st
  ensures NN(cs[x := cs[x] + 1])
  ensures cs[x] == 1 ==> x !in st && Good(st + [x], n)
            && RelS(cs[x := cs[x] + 1], st + [x], n, skip) && skip !in st + [x]
  ensures cs[x] != 1 ==> RelS(cs[x := cs[x] + 1], st, n, skip)
{
  var cs2 := cs[x := cs[x] + 1];
  if cs[x] == 1 {
    assert x !in st;
    GoodPush(st, x, n);
    forall j | 0 <= j < n && j != skip ensures (cs2[j] >= 2) <==> j in st + [x] {
      if j != x { assert cs2[j] == cs[j]; }
      assert (j in st + [x]) <==> (j in st || j == x);
    }
    assert (skip in st + [x]) <==> (skip in st || skip == x);
  } else {
    forall j | 0 <= j < n && j != skip ensures (cs2[j] >= 2) <==> j in st {
      if j != x { assert cs2[j] == cs[j]; }
    }
  }
}

lemma FinalRel(cs: seq<int>, st: seq<int>, n: int, i: int)
  requires |cs| == n && Good(st, n) && RelS(cs, st, n, i)
  requires 0 <= i < n && i !in st
  ensures cs[i] >= 2 ==> Good(st + [i], n) && RelS(cs, st + [i], n, -1)
  ensures cs[i] < 2 ==> RelS(cs, st, n, -1)
{
  if cs[i] >= 2 {
    GoodPush(st, i, n);
    forall j | 0 <= j < n ensures (cs[j] >= 2) <==> j in st + [i] {
      assert (j in st + [i]) <==> (j in st || j == i);
    }
  }
}

method Settle(c: array<int>) returns (moves: int, ghost steps: nat)
  requires forall i :: 0 <= i < c.Length ==> 0 <= c[i] <= 3
  modifies c
  ensures moves >= 0
  ensures steps <= 10 * c.Length + 10 + 20 * (c.Length * (3 * (c.Length * c.Length)))
  decreases c.Length
{
  steps := 0;
  steps := steps + 1;
  var n := c.Length;
  steps := steps + (1 + (n + 1));
  var stack := new int[n + 1];
  var top := 0;
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant 0 <= top <= k
    invariant c.Length == n && stack.Length == n + 1
    invariant forall i :: 0 <= i < n ==> 0 <= c[i] <= 3
    invariant Good(stack[..top], n)
    invariant forall j :: 0 <= j < n ==> ((j < k && c[j] >= 2) <==> j in stack[..top])
    invariant steps <= n + 3 + 8 * k
    decreases n - k
  {
    steps := steps + 2;
    steps := steps + 2;
    if c[k] >= 2 {
      steps := steps + 1;
      ghost var pre := stack[..top];
      GoodPush(pre, k, n);
      stack[top] := k;
      steps := steps + 1;
      top := top + 1;
      assert stack[..top] == pre + [k];
    }
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  moves := 0;
  PhiBound(c[..], 0, n);
  PhiNonneg(c[..], 0, n);
  ghost var phi0 := Phi(c[..], 0, n);
  while top > 0
    invariant 0 <= top <= n
    invariant c.Length == n && stack.Length == n + 1
    invariant Good(stack[..top], n)
    invariant RelS(c[..], stack[..top], n, -1)
    invariant NN(c[..])
    invariant moves >= 0
    invariant 2 * moves + Phi(c[..], 0, n) == phi0
    invariant Phi(c[..], 0, n) >= 0
    invariant phi0 <= n * (3 * (n * n))
    invariant steps <= 10 * n + 8 + 40 * moves
    decreases Phi(c[..], 0, n)
  {
    ghost var s0 := c[..];
    ghost var st0 := stack[..top];
    steps := steps + 2;
    steps := steps + 1;
    top := top - 1;
    steps := steps + 1;
    var i := stack[top];
    assert st0[|st0| - 1] == i;
    assert stack[..top] == st0[..|st0| - 1];
    Pop(s0, st0, n);
    ghost var st1 := stack[..top];
    steps := steps + 3;
    c[i] := c[i] - 2;
    ghost var s1 := c[..];
    assert s1 == s0[i := s0[i] - 2];
    PhiAdd(s0, i, -2, n);
    steps := steps + 1;
    moves := moves + 1;
    steps := steps + 1;
    if i > 0 {
      steps := steps + 5;
      ghost var sA := c[..];
      assert sA == s1;
      BumpRel(sA, stack[..top], n, i - 1, i);
      c[i - 1] := c[i - 1] + 1;
      assert c[..] == sA[i - 1 := sA[i - 1] + 1];
      PhiAdd(sA, i - 1, 1, n);
      steps := steps + 3;
      if c[i - 1] == 2 {
        steps := steps + 2;
        ghost var preA := stack[..top];
        stack[top] := i - 1;
        steps := steps + 1;
        top := top + 1;
        assert stack[..top] == preA + [i - 1];
        GoodBound(stack[..top], n);
      }
    }
    assert Phi(c[..], 0, n) == Phi(s1, 0, n) + (if i > 0 then W(i - 1, n) else 0);
    assert Good(stack[..top], n) && top <= n && NN(c[..]);
    assert RelS(c[..], stack[..top], n, i);
    assert i !in stack[..top];
    steps := steps + 2;
    if i + 1 < n {
      steps := steps + 5;
      ghost var sB := c[..];
      BumpRel(sB, stack[..top], n, i + 1, i);
      c[i + 1] := c[i + 1] + 1;
      assert c[..] == sB[i + 1 := sB[i + 1] + 1];
      PhiAdd(sB, i + 1, 1, n);
      steps := steps + 3;
      if c[i + 1] == 2 {
        steps := steps + 2;
        ghost var preB := stack[..top];
        stack[top] := i + 1;
        steps := steps + 1;
        top := top + 1;
        assert stack[..top] == preB + [i + 1];
        GoodBound(stack[..top], n);
      }
    }
    assert Phi(c[..], 0, n)
        == Phi(s1, 0, n) + (if i > 0 then W(i - 1, n) else 0)
                         + (if i + 1 < n then W(i + 1, n) else 0);
    assert Good(stack[..top], n) && top <= n && NN(c[..]);
    assert RelS(c[..], stack[..top], n, i);
    assert i !in stack[..top];
    FinalRel(c[..], stack[..top], n, i);
    steps := steps + 2;
    if c[i] >= 2 {
      steps := steps + 1;
      ghost var preC := stack[..top];
      stack[top] := i;
      steps := steps + 1;
      top := top + 1;
      assert stack[..top] == preC + [i];
    }
    WStep(i, n);
    assert i > 0 || W(i - 1, n) == 0;
    assert i + 1 < n || W(i + 1, n) == 0;
    assert Phi(c[..], 0, n) == Phi(s0, 0, n) - 2;
    assert Good(stack[..top], n);
    GoodBound(stack[..top], n);
    PhiNonneg(c[..], 0, n);
  }
  steps := steps + 1;
}

method Solve(n: int, a_list: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  ensures steps <= 21 * n + 12 + 20 * (n * (3 * (n * n))) + 2 * |output|
  decreases n
{
  steps := 0;
  steps := steps + n;
  var c := new int[n];
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant c.Length == n
    invariant forall j :: 0 <= j < k ==> 0 <= c[j] <= 3
    invariant steps <= n + 5 * k
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
  var left := 0;
  k := 0;
  ghost var b := steps;
  while k < n
    invariant 0 <= k <= n
    invariant steps <= b + 5 * k
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
  IntToStringDigits(moves);
  IntToStringDigits(left);
  output := IntToString(moves) + " " + IntToString(left);
}

import opened Prelude
