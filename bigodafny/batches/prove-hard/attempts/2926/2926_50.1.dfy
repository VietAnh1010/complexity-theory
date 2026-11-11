// --- Python ---------------------------------------------------------
// l=[2	,3	,5	,7	,11	,13	,17	,19	,23	,29	,31	,37	,41	,43	,47	,53	,59	,61	,67	,71
// ,73	,79	,83	,89	,97	,101	,103	,107	,109	,113	,127	,131	,137	,139	,149	,151	,157	,163	,167	,173
// ,179	,181	,191	,193	,197	,199	,211	,223	,227	,229	,233	,239	,241]
// n=int(input())
// l1=[1 for i in range(n)]
// if n==2 :
//     print("-1")
//     exit()
// for i in range(n-1) :
//     l1[i]=2*l[i+1]
//     l1[-1]*=l[i+1]
// for x in l1 :
//     print(x)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

ghost function DigA(xs: seq<int>): seq<int>
{
  seq(|xs|, k requires 0 <= k < |xs| => 1 + Digits(xs[k]))
}

ghost function StrA(xs: seq<int>): seq<string>
{
  seq(|xs|, k requires 0 <= k < |xs| => IntToString(xs[k]))
}

lemma PrefixDig(xs: seq<int>, t: nat)
  requires t <= |xs|
  ensures PrefixSum(DigA(xs), t) == t + SumLen(StrA(xs)[..t])
  decreases t
{
  if t > 0 {
    PrefixDig(xs, t - 1);
    assert StrA(xs)[..t] == StrA(xs)[..t - 1] + [StrA(xs)[t - 1]];
    SumLenSnoc(StrA(xs)[..t - 1], StrA(xs)[t - 1]);
    IntToStringDigits(xs[t - 1]);
  }
}

lemma SumSeqDig(xs: seq<int>)
  ensures SumSeq(DigA(xs)) == |xs| + SumLen(StrA(xs))
{
  PrefixSumIsSumSeq(DigA(xs));
  PrefixDig(xs, |xs|);
  assert StrA(xs)[..|xs|] == StrA(xs);
}

method Solve(n: int) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * n + 2 * |output| + 900
{
  steps := 0;
  steps := steps + 53;
  var primes := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241];
  steps := steps + 1;
  if n == 2 {
    output := "-1\n";
  } else if n <= 0 {
    output := "";
  } else {
    steps := steps + n;
    var l1 := seq(n, _ /* _v0 */ => 1);
    var last := 1;
    var i := 0;
    while i < n - 1 && i + 1 < |primes|
      invariant 0 <= i
      invariant |l1| == n
      invariant i <= 54
      invariant steps <= 54 + n + 15 * i
      decreases n - 1 - i
    {
      steps := steps + (4 + if i < n - 1 then 3 else 0);
      steps := steps + 4;
      l1 := l1[i := 2 * primes[i + 1]];
      steps := steps + 3;
      last := last * primes[i + 1];
      steps := steps + 1;
      i := i + 1;
    }
    steps := steps + (3 + if i < n - 1 then 3 else 0);
    steps := steps + 2;
    l1 := l1[n - 1 := last];
    steps := steps + (n + SumSeq(seq(n, k requires 0 <= k < n => 1 + Digits(l1[k]))));
    var lines := seq(n, k requires 0 <= k < n => IntToString(l1[k]));
    steps := steps + (SumLen(lines) + |lines| + |"\n"|);
    output := Join(lines, "\n") + "\n";
    SumSeqDig(l1);
    assert DigA(l1) == seq(n, k requires 0 <= k < n => 1 + Digits(l1[k]));
    assert StrA(l1) == lines;
    JoinLen(lines, "\n");
  }
}

import opened Prelude
