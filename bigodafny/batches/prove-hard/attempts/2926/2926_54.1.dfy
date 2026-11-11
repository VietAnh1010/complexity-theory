// --- Python ---------------------------------------------------------
// isprime = [1 for i in range(2003)]
//
// isprime[0] = 0
// isprime[1] = 0
// for i in range(2,2000,1):
//     if(isprime[i]):
//         j = i*i
//         while j < 2000:
//             isprime[j] = 0
//             j += i
//
// prime = []
// for i in range(2,2000,1):
//     if(isprime[i]):
//         prime.append(i)
//
// n = int(input())
// if(n==2):
//     print('-1')
//     exit(0)
//
// for i in range(n):
//     val = 1
//     for j in range(n):
//         if i==j : continue
//         val *= prime[j]
//     print(val)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 24100000 + 16 * (n * n) + 2 * |output| + 2
{
  steps := 0;
  steps := steps + 2003;
  var isprime: seq<bool> := seq(2003, _ /* _v0 */ => true);
  steps := steps + 1;
  isprime := isprime[0 := false];
  steps := steps + 1;
  isprime := isprime[1 := false];
  var i := 2;
  while i < 2000
    invariant 2 <= i <= 2000
    invariant |isprime| == 2003
    invariant steps <= 2005 + (i - 2) * 12020
    decreases 2000 - i
  {
    steps := steps + 2;
    steps := steps + 1;
    if isprime[i] {
      steps := steps + 1;
      var j := i * i;
      SqGe4(i);
      ghost var j0 := j;
      ghost var s0 := steps;
      while j < 2000
        invariant |isprime| == 2003
        invariant j0 >= 4 && j >= j0
        invariant steps <= s0 + 3 * (j - j0)
        invariant j == j0 || j < 2000 + i
        decreases 2000 - j
      {
        steps := steps + 2;
        steps := steps + 1;
        isprime := isprime[j := false];
        steps := steps + 1;
        j := j + i;
      }
      steps := steps + 1;
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  var primes: seq<int> := [];
  var k := 2;
  ghost var s2 := steps;
  while k < 2000
    invariant 2 <= k <= 2000
    invariant |isprime| == 2003
    invariant steps <= s2 + 6 * (k - 2)
    decreases 2000 - k
  {
    steps := steps + 2;
    steps := steps + 1;
    if isprime[k] {
      steps := steps + (1 + |[k]|);
      primes := primes + [k];
    }
    steps := steps + 1;
    k := k + 1;
  }
  steps := steps + 1;
  steps := steps + 1;
  assert steps <= 24100000;
  if n == 2 {
    output := "-1";
  } else {
    var lines: seq<string> := [];
    var ii := 0;
    ghost var base := steps;
    ghost var K: nat := if n > 0 then 9 * n + 6 else 0;
    SqBound(n);
    while ii < n
      invariant 0 <= ii <= (if n > 0 then n else 0)
      invariant |lines| == ii
      invariant steps <= base + ii * K + SumLen(lines)
      decreases n - ii
    {
      steps := steps + 2;
      ghost var s1 := steps;
      var val := 1;
      var jj := 0;
      while jj < n
        invariant 0 <= jj <= n
        invariant steps <= s1 + 9 * jj
        decreases n - jj
      {
        steps := steps + 2;
        steps := steps + (2 + if ii != jj then 2 else 0);
        if ii != jj && jj < |primes| {
          steps := steps + 2;
          val := val * primes[jj];
        }
        steps := steps + 1;
        jj := jj + 1;
      }
      steps := steps + 1;
      steps := steps + (1 + Digits(val) + |[IntToString(val)]|);
      IntToStringDigits(val);
      SumLenSnoc(lines, IntToString(val));
      CostMulDistrib(ii, 1, ii + 1, K);
      lines := lines + [IntToString(val)];
      steps := steps + 1;
      ii := ii + 1;
    }
    steps := steps + 1;
    steps := steps + (SumLen(lines) + |lines|);
    if |lines| >= 1 {
      JoinLen(lines, "\n");
    }
    output := Join(lines, "\n");
  }
}

import opened Prelude

lemma SqGe4(i: int)
  requires i >= 2
  ensures i * i >= 4
{
  assert i * i >= 2 * i by { assert (i - 2) * i >= 0; }
}

lemma SqBound(n: int)
  ensures n * n >= 0
  ensures n >= 1 ==> n * n >= n
  ensures n >= 1 ==> n * (9 * n + 6) == 9 * (n * n) + 6 * n
{
  if n >= 1 {
    assert n * n >= n * 1;
  }
}
