// --- Python ---------------------------------------------------------
// n= int(input())
// seq= list(input())
// 
// if seq.count(')')!=seq.count('('):
// 	print(-1)
// else:
// 	a,b=[],[]
// 	for i in range(len(seq)):
// 		if seq[i]==')':
// 			a.append(i)
// 		else:
// 			b.append(i)
// 	c=[]
// 	for i in range(len(a)):
// 		if b[i]>a[i]:
// 			c.append(a[i])
// 			c.append(b[i])
// 	c.sort()
// 	start=0
// 	sum=0
// 	for i in range(len(c)-1):
// 		if c[i]!=c[i+1]-1:
// 			sum+=c[i]-c[start]+1
// 			start=i+1
// 		else:
// 			if i==len(c)-2:
// 				sum+=c[i+1]-c[start]+1
// 			
// 	print(sum)
// 	
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

method Solve(n: int, s: string)
    returns (output: string, ghost steps: nat)
    ensures steps <= 21 * |s| + 38 * |s| + 2 * NLogN(2 * |s|) + 11 + |output|
{
  steps := 0;
  var a: seq<int> := [];
  var b: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |a| + |b| == i
    invariant steps <= 8 * i
    decreases |s| - i
  {
    steps := steps + 3;
    steps := steps + 2;
    if s[i] == ')' {
      steps := steps + (1 + |[i]|);
      a := a + [i];
    } else {
      steps := steps + (1 + |[i]|);
      b := b + [i];
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 2;
  steps := steps + 3;
  if |a| != |b| {
    output := "-1";
  } else {
    var c: seq<int> := [];
    i := 0;
    while i < |a|
      invariant 0 <= i <= |a|
      invariant |a| + |b| == |s|
      invariant |c| <= 2 * i
      invariant steps <= 8 * |s| + 5 + 13 * i
      decreases |a| - i
    {
      steps := steps + 3;
      steps := steps + 3;
      if b[i] > a[i] {
        steps := steps + (4 + |[a[i], b[i]]|);
        c := c + [a[i], b[i]];
      }
      steps := steps + 1;
      i := i + 1;
    }
    steps := steps + 2;
    steps := steps + SortCost(|c|);
    SortCostWithin(|c|, 2 * |s|);
    c := SortInts(c);
    ghost var s1 := steps;
    var start := 0;
    var sum := 0;
    i := 0;
    while i < |c| - 1
      invariant 0 <= start <= i <= |c|
      invariant steps <= s1 + 19 * i
      decreases |c| - 1 - i
    {
      steps := steps + 4;
      steps := steps + 5;
      if c[i] != c[i + 1] - 1 {
        steps := steps + 5;
        sum := sum + (c[i] - c[start] + 1);
        steps := steps + 1;
        start := i + 1;
      } else {
        steps := steps + 3;
        if i == |c| - 2 {
          steps := steps + 6;
          sum := sum + (c[i + 1] - c[start] + 1);
        }
      }
      steps := steps + 1;
      i := i + 1;
    }
    steps := steps + 3;
    steps := steps + Digits(sum);
    output := IntToString(sum);
    IntToStringDigits(sum);
  }
}

method CountChar661(s: string, ch: char)
    returns (cnt: int, ghost steps: nat)
{
  steps := 0;
  cnt := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    steps := steps + 3;
    steps := steps + 2;
    if s[i] == ch {
      steps := steps + 1;
      cnt := cnt + 1;
    }
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 2;
}

import opened Prelude
