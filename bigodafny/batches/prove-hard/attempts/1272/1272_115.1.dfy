// --- Python ---------------------------------------------------------
// n=int(input())
// list1=[]
// for i in range(n):
//     s=input()
//     list1.append(s)
// # list1.sort()
// for i in range(n-1):
//     for j in range(i,n):
//         if(len(list1[i])>len(list1[j])):
//             list1[i],list1[j]=list1[j],list1[i]
// f=0
// for i in range(n-1):
//     # if(list1[i] in list1[i+1]):
//     x=list1[i+1].find(list1[i])
//     if(x>=0):
//         continue
//     else:
//         f=1
// if(f==0):
//     print("YES")
//     for i in range(n):
//         print(list1[i])
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

function ContainsFrom1272a(hay: string, needle: string, pos: nat): bool
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  if pos + |needle| > |hay| then
    false
  else if hay[pos .. pos + |needle|] == needle then
    true
  else
    ContainsFrom1272a(hay, needle, pos + 1)
}

ghost function ContainsFrom1272a_steps(hay: string, needle: string, pos: nat): nat
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  5 + if pos + |needle| > |hay| then 0 else 5 + if hay[pos .. pos + |needle|] == needle then 0 else 1 + ContainsFrom1272a_steps(hay, needle, pos + 1)
}

function Contains1272a(hay: string, needle: string): bool
{
  |needle| == 0 || ContainsFrom1272a(hay, needle, 0)
}

ghost function Contains1272a_steps(hay: string, needle: string): nat
{
  3 + if |needle| == 0 then 0 else ContainsFrom1272a_steps(hay, needle, 0)
}

lemma ContainsFromBound(hay: string, needle: string, pos: nat)
  requires 1 <= |needle|
  requires pos <= |hay|
  ensures ContainsFrom1272a_steps(hay, needle, pos) <= 11 * (|hay| - pos) + 10
  decreases |hay| - pos
{
  if pos + |needle| <= |hay| && hay[pos .. pos + |needle|] != needle {
    ContainsFromBound(hay, needle, pos + 1);
  }
}

lemma ContainsBound(hay: string, needle: string)
  ensures Contains1272a_steps(hay, needle) <= 13 + 11 * |hay|
{
  if |needle| != 0 { ContainsFromBound(hay, needle, 0); }
}

method Solve(n: int, strings: seq<string>)
    returns (output: string, ghost steps: nat)
  requires n == |strings|
  ensures steps <= n * (12 * n + 5) + n * (21 + 11 * SumLen(strings)) + 7 * n + 20 + |output|
{
  steps := 0;
  ghost var L := SumLen(strings);
  forall x | 0 <= x < |strings| ensures |strings[x]| <= L {
    SumLenElem(strings, x);
  }
  var list1 := strings;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n
    invariant |list1| == n
    invariant forall x :: 0 <= x < n ==> |list1[x]| <= L
    invariant steps <= i * (12 * n + 5)
    decreases n - 1 - i
  {
    steps := steps + 3;
    ghost var base := steps;
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant |list1| == n
      invariant forall x :: 0 <= x < n ==> |list1[x]| <= L
      invariant steps <= base + 12 * (j - i)
      decreases n - j
    {
      steps := steps + 2;
      steps := steps + 5;
      if |list1[i]| > |list1[j]| {
        steps := steps + 1;
        var tmp := list1[i];
        steps := steps + 3;
        list1 := list1[i := list1[j]][j := tmp];
      }
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + 1;
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, 12 * n + 5);
    i := i + 1;
  }
  CostMulMonoLeft(i, n, 12 * n + 5);
  steps := steps + 2;
  ghost var S1 := steps;
  var f := 0;
  var k := 0;
  while k < n - 1
    invariant 0 <= k <= n
    invariant |list1| == n
    invariant forall x :: 0 <= x < n ==> |list1[x]| <= L
    invariant steps <= S1 + k * (21 + 11 * L)
    decreases n - 1 - k
  {
    steps := steps + 3;
    ContainsBound(list1[k + 1], list1[k]);
    CostMulDistrib(k, 1, k + 1, 21 + 11 * L);
    steps := steps + (4 + Contains1272a_steps(list1[k + 1], list1[k]));
    if !Contains1272a(list1[k + 1], list1[k]) {
      f := 1;
    }
    steps := steps + 1;
    k := k + 1;
  }
  CostMulMonoLeft(k, n, 21 + 11 * L);
  steps := steps + 2;
  steps := steps + 1;
  ghost var S2 := steps;
  if f == 0 {
    steps := steps + 1;
    var lines: seq<string> := ["YES"];
    var m := 0;
    while m < n
      invariant 0 <= m <= n
      invariant |lines| == m + 1
      invariant steps <= S2 + 1 + 7 * m
      decreases n - m
    {
      steps := steps + 2;
      steps := steps + (2 + |[list1[m]]|);
      lines := lines + [list1[m]];
      steps := steps + 1;
      m := m + 1;
    }
    steps := steps + 1;
    steps := steps + (SumLen(lines) + |lines|);
    output := Join(lines, "\n");
    JoinLen(lines, "\n");
  } else {
    output := "NO";
  }
}

import opened Prelude
