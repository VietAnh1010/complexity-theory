// 1105_B. Zuhair and Strings  (problem 2231, solution 2231_194)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,k=input().split()
// n=int(n)
// k=int(k)
// s=input()
//
//
// arr=[]
// f=s[0]
// z=''
// for i in range (len(s)):
//     if s[i]==f:
//         z=z+s[i]
//     else:
//         f=s[i]
//         arr.append(z)
//         z=f
// arr.append(z)
// arr
//
// arr.sort()
//
// f=arr[0][0]
// c=0
// i=0
// q=[]
// while i<len(arr):
//     if f in arr[i]:
//         c=c+int(len(arr[i])/k)
//     else:
//         q.append(c)
//         c=0
//
//         f=arr[i][0]
//         i=i-1
//         pass
//     i=i+1
// q.append(c)
//
// print(max(q))
//
//
//
//
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// ---- proof-only scaffolding for the complexity bound (see
// solutions-proved/nlogn/603/603_284.dfy for the same argument). Comparator
// cost of `less` inside Sort/Merge is not charged separately -- same
// simplification as the rest of this corpus's nlogn scaffolds. ------------

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

// |arr| never exceeds the number of characters scanned so far: each `arr`
// append consumes at least one character not yet flushed.
lemma CeilLog2MonotoneUse(m: nat, n: nat)
  requires m <= n
  ensures 2 * m * (CeilLog2(m) + 1) + 1 <= 2 * n * (CeilLog2(n) + 1) + 1
{
  CeilLog2Monotone(m, n);
  var Lm := CeilLog2(m) + 1;
  var Ln := CeilLog2(n) + 1;
  assert Lm <= Ln;
  MulMonoRight(2 * m, Lm, Ln);
  assert (2 * m) * Lm <= (2 * m) * Ln;
  MulMonoRight(Ln, 2 * m, 2 * n);
  assert Ln * (2 * m) <= Ln * (2 * n);
  assert (2 * m) * Ln == Ln * (2 * m);
  assert Ln * (2 * n) == (2 * n) * Ln;
  assert (2 * m) * Lm <= (2 * n) * Ln;
  assert 2 * m * (CeilLog2(m) + 1) == (2 * m) * Lm;
  assert 2 * n * (CeilLog2(n) + 1) == (2 * n) * Ln;
}

method Solve(a: int, b: int, string_: string) returns (output: string, ghost steps: nat)
  requires b >= 1
  requires |string_| >= 1
  ensures steps <= 2 * |string_| * (CeilLog2(|string_|) + 1) + 8 * |string_| + 15
{
  steps := 1;
  var k := b;
  var s := string_;
  var arr: seq<string> := [];
  if |s| > 0 {
    var f := s[0];
    var z: string := "";
    var i := 0;
    while i < |s|
      invariant 0 <= i <= |s|
      invariant i == 0 ==> f == s[0]
      invariant i >= 1 ==> |z| >= 1
      invariant forall x :: x in arr ==> |x| >= 1
      invariant |arr| + |z| <= i
      invariant steps <= 1 + 3 * i
      decreases |s| - i
    {
      if s[i] == f {
        z := z + [s[i]];
      } else {
        f := s[i];
        arr := arr + [z];
        z := [s[i]];
      }
      i := i + 1;
      steps := steps + 3;
    }
    arr := arr + [z];
    steps := steps + 1;
  }
  assert |arr| >= 1;
  assert |arr| <= |s|;
  SortStringsKeepsElems(arr);
  SortCostTreeBound(|arr|);
  CeilLog2MonotoneUse(|arr|, |s|);
  steps := steps + SortCost(|arr|);
  var sortedArr := SortStrings(arr);
  assert forall x :: x in sortedArr ==> |x| >= 1;
  arr := sortedArr;
  var curChar := arr[0][0];
  var c := 0;
  var q: seq<int> := [];
  var idx := 0;
  ghost var base := steps;
  while idx < |arr|
    invariant 0 <= idx <= |arr|
    invariant forall x :: x in arr ==> |x| >= 1
    invariant steps <= base + 4 * idx
    decreases |arr| - idx
  {
    if arr[idx][0] == curChar {
      c := c + FloorDiv(|arr[idx]|, k);
    } else {
      q := q + [c];
      c := FloorDiv(|arr[idx]|, k);
      curChar := arr[idx][0];
    }
    idx := idx + 1;
    steps := steps + 4;
  }
  q := q + [c];
  steps := steps + 1;
  output := IntToString(MaxSeq(q));
  steps := steps + 1;
}
