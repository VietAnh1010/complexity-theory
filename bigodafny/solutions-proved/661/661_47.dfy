// 1323_C. Unusual Competitions  (problem 661, solution 661_47)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
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

// PROOF NOTE (relation: confirms).
// The scan, the pairing pass and the final merge of runs are each O(|s|). The
// pairing pass emits two indices per matched pair, so |c| <= 2|a| = |s|, and
// the sort of c is folded into NLogN(|s|) by the prelude's SortCostWithin.

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|s|) + 9 * |s| + 4
{
  steps := 1;
  var a: seq<int> := [];
  var b: seq<int> := [];
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |a| + |b| == i
    invariant steps == 1 + 3 * i
    decreases |s| - i
  {
    if s[i] == ')' { a := a + [i]; } else { b := b + [i]; }
    i := i + 1;
    steps := steps + 3;
  }
  if |a| != |b| {
    output := "-1";
    steps := steps + 1;
  } else {
    var c: seq<int> := [];
    i := 0;
    while i < |a|
      invariant 0 <= i <= |a|
      invariant |c| <= 2 * i
      invariant steps == 1 + 3 * |s| + 3 * i
      decreases |a| - i
    {
      if b[i] > a[i] {
        c := c + [a[i], b[i]];
      }
      i := i + 1;
      steps := steps + 3;
    }
    assert 2 * |a| == |s|;
    assert |c| <= |s|;
    ghost var k := |c|;
    steps := steps + SortCost(k);
    SortCostWithin(k, |s|);
    c := SortInts(c);
    assert |c| == k;
    ghost var base3 := steps;
    var start := 0;
    var sum := 0;
    i := 0;
    while i < |c| - 1
      invariant 0 <= start <= i
      invariant i <= |c|
      invariant steps == base3 + 3 * i
      decreases |c| - 1 - i
    {
      if c[i] != c[i+1] - 1 {
        sum := sum + (c[i] - c[start] + 1);
        start := i + 1;
      } else {
        if i == |c| - 2 {
          sum := sum + (c[i+1] - c[start] + 1);
        }
      }
      i := i + 1;
      steps := steps + 3;
    }
    output := IntToString(sum);
    steps := steps + 2;
  }
}

method CountChar661(s: string, ch: char) returns (cnt: int)
{
  cnt := 0;
  var i := 0;
  while i < |s|
    decreases |s| - i
  {
    if s[i] == ch { cnt := cnt + 1; }
    i := i + 1;
  }
}
