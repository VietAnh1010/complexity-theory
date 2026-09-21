// 141_A. Amusing Joke  (problem 2962, solution 2962_1968)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=input()
// l=input()
// m=input()
// a=len(n)+len(l)
// c=0
// n=list(n)+list(l)
// m=list(m)
// d=[]
// d=d+m
// for i in range(len(n)):
//     if n[i] not in m:
//         c=1
//         break
//     else:
//         d.remove(n[i])
//         m.remove(n[i])
// if c==1:
//     print("NO")
// elif len(d)!=0:
//     print("NO")
// else:
//     print("YES")
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MulSuccDistrib(i: int, K: int)
  ensures (i + 1) * K == i * K + K
{}

lemma MulMonoLeft(a: int, b: int, K: int)
  requires 0 <= a <= b
  requires K >= 0
  ensures a * K <= b * K
{}

method Solve(first_name: seq<string>, second_name: seq<string>, jumbled_name: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= (|first_name| + |second_name|) * (3 * |jumbled_name| + 7) + |second_name| + 5
{
  steps := 1;
  var need := first_name + second_name;
  steps := steps + |second_name|;
  var remaining := jumbled_name;
  var c := 0;
  var i := 0;
  steps := steps + 3;
  while i < |need| && c == 0
    invariant 0 <= i <= |need|
    invariant |remaining| <= |jumbled_name|
    invariant |need| == |first_name| + |second_name|
    invariant steps <= i * (3 * |jumbled_name| + 7) + |second_name| + 4
    decreases |need| - i
  {
    var ch := need[i];
    var idx := -1;
    var j := 0;
    steps := steps + 3;
    while j < |remaining|
      invariant 0 <= j <= |remaining|
      invariant idx == -1 || (0 <= idx < j && remaining[idx] == ch)
      invariant steps <= i * (3 * |jumbled_name| + 7) + |second_name| + 7 + 2 * j
      decreases |remaining| - j
    {
      if idx == -1 && remaining[j] == ch { idx := j; }
      j := j + 1;
      steps := steps + 2;
    }
    if idx == -1 {
      c := 1;
      steps := steps + 1;
    } else {
      remaining := remaining[..idx] + remaining[idx + 1..];
      steps := steps + 3 + |jumbled_name|;
    }
    MulSuccDistrib(i, 3 * |jumbled_name| + 7);
    i := i + 1;
    steps := steps + 1;
  }
  MulMonoLeft(i, |need|, 3 * |jumbled_name| + 7);
  if c == 1 {
    output := "NO";
  } else if |remaining| != 0 {
    output := "NO";
  } else {
    output := "YES";
  }
  steps := steps + 1;
}
