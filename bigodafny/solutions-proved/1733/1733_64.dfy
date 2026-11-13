// 1427_D. Unshuffling a Deck  (problem 1733, solution 1733_64)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// input=sys.stdin.readline
// n=int(input())
// c=list(map(int,input().split()))
// ac=[]
// f=int(n%2==1)
// for tar in range(1,n+1)[::-1]:
//     split=[]
//     cnt=0
//     if f:
//         for i in range(n):
//             cnt+=1
//             if tar<=c[i]:
//                 split.append(cnt)
//                 cnt=0
//     else:
//         for i in range(n)[::-1]:
//             cnt+=1
//             if tar<=c[i]:
//                 split.append(cnt)
//                 cnt=0
//     if cnt:
//         split.append(cnt)
//     if f==0:
//         split.reverse()
//     if len(split)==1:
//         f^=1
//         continue
//     ac.append(split)
//     new=[]
//     s=0
//     for i in range(len(split)):
//         new.append(c[s:s+split[i]])
//         s+=split[i]
//     new.reverse()
//     new_arr=[]
//     for tmp in new:
//         new_arr+=tmp
//     c=new_arr
//     f^=1
// print(len(ac))
// for arr in ac:
//     print(len(arr),*arr)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ReverseInt(s: seq<int>): seq<int>
  ensures |ReverseInt(s)| == |s|
  decreases |s|
{
  if |s| == 0 then [] else ReverseInt(s[1..]) + [s[0]]
}

function ReverseListOfLists(s: seq<seq<int>>): seq<seq<int>>
  ensures |ReverseListOfLists(s)| == |s|
  decreases |s|
{
  if |s| == 0 then [] else ReverseListOfLists(s[1..]) + [s[0]]
}

function FormatLenAndElems(l: seq<int>): string
{
  if |l| == 0 then IntToString(0) else IntToString(|l|) + " " + JoinInts(l, " ")
}

function SumInts(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + SumInts(s[1..])
}

lemma SumIntsAppend(a: seq<int>, b: seq<int>)
  ensures SumInts(a + b) == SumInts(a) + SumInts(b)
  decreases |a|
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert (a + b)[1..] == a[1..] + b;
    SumIntsAppend(a[1..], b);
  }
}

lemma SumIntsReverse(s: seq<int>)
  ensures SumInts(ReverseInt(s)) == SumInts(s)
  decreases |s|
{
  if |s| == 0 {
  } else {
    SumIntsReverse(s[1..]);
    SumIntsAppend(ReverseInt(s[1..]), [s[0]]);
  }
}

lemma SumIntsNonneg(s: seq<int>)
  requires forall t :: 0 <= t < |s| ==> s[t] >= 0
  ensures SumInts(s) >= 0
  decreases |s|
{
  if |s| == 0 {
  } else {
    SumIntsNonneg(s[1..]);
  }
}

lemma SplitPrefixSum(split: seq<int>, k: int)
  requires 0 <= k < |split|
  ensures SumInts(split[..k+1]) == SumInts(split[..k]) + split[k]
{
  assert split[..k+1] == split[..k] + [split[k]];
  SumIntsAppend(split[..k], [split[k]]);
}

lemma SplitPrefixBound(split: seq<int>, k: int)
  requires 0 <= k < |split|
  requires forall t :: 0 <= t < |split| ==> split[t] >= 1
  ensures SumInts(split[..k+1]) <= SumInts(split)
{
  assert split == split[..k+1] + split[k+1..];
  SumIntsAppend(split[..k+1], split[k+1..]);
  SumIntsNonneg(split[k+1..]);
}

lemma ReverseIntElems(s: seq<int>)
  ensures forall t :: 0 <= t < |s| ==> ReverseInt(s)[t] == s[|s| - 1 - t]
  decreases |s|
{
  if |s| == 0 {
  } else {
    ReverseIntElems(s[1..]);
  }
}

ghost function SumLens(s: seq<seq<int>>): nat
  decreases |s|
{
  if |s| == 0 then 0 else |s[0]| + SumLens(s[1..])
}

lemma SumLensSnoc(s: seq<seq<int>>, x: seq<int>)
  ensures SumLens(s + [x]) == SumLens(s) + |x|
  decreases |s|
{
  if |s| > 0 {
    assert (s + [x])[1..] == s[1..] + [x];
    SumLensSnoc(s[1..], x);
  }
}

lemma SumLensRev(s: seq<seq<int>>)
  ensures SumLens(ReverseListOfLists(s)) == SumLens(s)
  decreases |s|
{
  if |s| > 0 {
    SumLensRev(s[1..]);
    SumLensSnoc(ReverseListOfLists(s[1..]), s[0]);
  }
}

lemma SplitLen(s: seq<int>)
  requires forall t :: 0 <= t < |s| ==> s[t] >= 1
  ensures |s| <= SumInts(s)
  decreases |s|
{
  if |s| > 0 { SplitLen(s[1..]); }
}

ghost function LineCost(l: seq<int>): nat
{
  if |l| == 0 then 3
  else Digits(|l|) + 1 + SumDigits(l) + |l| + (SumDigits(l) + |l|) + 3
}

lemma LineCostBound(l: seq<int>)
  ensures LineCost(l) <= 4 * |FormatLenAndElems(l)| + 4
{
  if |l| > 0 {
    IntToStringDigits(|l|);
    JoinIntsLen(l, " ");
  }
}

method Solve(a: int, b_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |b_list| == a
  ensures steps <= 40 * (a * a) + 60 * a + 100 + 12 * |output|
{
  steps := 1;
  var n := a;
  var c: seq<int> := b_list;
  var ac: seq<seq<int>> := [];
  var f := if n % 2 == 1 then 1 else 0;
  var tar := n;
  steps := steps + 4;
  ghost var K: nat := 40 * n + 40;
  ghost var it: nat := 0;
  ghost var base := steps;
  while tar >= 1
    invariant 0 <= tar <= n
    invariant it == n - tar
    invariant |c| == n
    invariant |ac| <= it
    invariant forall j :: 0 <= j < |ac| ==> |ac[j]| <= n
    invariant steps <= base + it * K
    invariant K == 40 * n + 40
    decreases tar
  {
    ghost var st0 := steps;
    var split: seq<int> := [];
    var cnt := 0;
    if f == 1 {
      var i := 0;
      ghost var s0 := steps;
      while i < |c|
        invariant 0 <= i <= |c|
        invariant cnt >= 0
        invariant SumInts(split) + cnt == i
        invariant forall t :: 0 <= t < |split| ==> split[t] >= 1
        invariant steps == s0 + 10 * i
        decreases |c| - i
      {
        cnt := cnt + 1;
        if tar <= c[i] {
          SumIntsAppend(split, [cnt]);
          split := split + [cnt];
          cnt := 0;
        }
        i := i + 1;
        steps := steps + 10;
      }
      steps := steps + 1;
    } else {
      var i := |c| - 1;
      ghost var s0 := steps;
      while i >= 0
        invariant -1 <= i <= |c| - 1
        invariant cnt >= 0
        invariant SumInts(split) + cnt == |c| - 1 - i
        invariant forall t :: 0 <= t < |split| ==> split[t] >= 1
        invariant steps == s0 + 10 * (|c| - 1 - i)
        decreases i + 1
      {
        cnt := cnt + 1;
        if tar <= c[i] {
          SumIntsAppend(split, [cnt]);
          split := split + [cnt];
          cnt := 0;
        }
        i := i - 1;
        steps := steps + 10;
      }
      steps := steps + 1;
    }
    assert steps <= st0 + 10 * n + 2;
    if cnt != 0 {
      SumIntsAppend(split, [cnt]);
      split := split + [cnt];
    }
    steps := steps + 2;
    assert SumInts(split) == |c|;
    assert forall t :: 0 <= t < |split| ==> split[t] >= 1;
    SplitLen(split);
    if f == 0 {
      ghost var before := split;
      split := ReverseInt(split);
      steps := steps + |before| + 1;
      SumIntsReverse(before);
      ReverseIntElems(before);
    }
    assert SumInts(split) == |c|;
    assert forall t :: 0 <= t < |split| ==> split[t] >= 1;
    assert |split| <= n;
    assert steps <= st0 + 11 * n + 6;
    if |split| == 1 {
      f := 1 - f;
      steps := steps + 3;
    } else {
      ac := ac + [split];
      steps := steps + 1;
      var segs: seq<seq<int>> := [];
      var s := 0;
      var k := 0;
      ghost var s1 := steps;
      while k < |split|
        invariant 0 <= k <= |split|
        invariant 0 <= s <= |c|
        invariant s == SumInts(split[..k])
        invariant |segs| == k
        invariant SumLens(segs) == s
        invariant steps == s1 + 10 * k
        decreases |split| - k
      {
        SplitPrefixSum(split, k);
        SplitPrefixBound(split, k);
        SumLensSnoc(segs, c[s..s + split[k]]);
        segs := segs + [c[s..s + split[k]]];
        s := s + split[k];
        k := k + 1;
        steps := steps + 10;
      }
      assert split[..k] == split;
      steps := steps + 1;
      var revSegs := ReverseListOfLists(segs);
      steps := steps + |segs| + 1;
      SumLensRev(segs);
      var newArr: seq<int> := [];
      var t := 0;
      ghost var s2 := steps;
      while t < |revSegs|
        invariant 0 <= t <= |revSegs|
        invariant |newArr| == SumLens(revSegs[..t])
        invariant steps == s2 + 6 * t + SumLens(revSegs[..t])
        decreases |revSegs| - t
      {
        assert revSegs[..t + 1] == revSegs[..t] + [revSegs[t]];
        SumLensSnoc(revSegs[..t], revSegs[t]);
        newArr := newArr + revSegs[t];
        t := t + 1;
        steps := steps + 6 + |revSegs[t - 1]|;
      }
      assert revSegs[..t] == revSegs;
      steps := steps + 1;
      c := newArr;
      f := 1 - f;
      steps := steps + 2;
    }
    CostMulDistrib(it, 1, it + 1, K);
    assert steps <= st0 + 40 * n + 40;
    tar := tar - 1;
    it := it + 1;
    steps := steps + 2;
    assert steps <= st0 + K;
  }
  var lines: seq<string> := [];
  var idx := 0;
  ghost var s3 := steps;
  while idx < |ac|
    invariant 0 <= idx <= |ac|
    invariant |lines| == idx
    invariant forall j :: 0 <= j < idx ==> lines[j] == FormatLenAndElems(ac[j])
    invariant steps <= s3 + 4 * SumLen(lines) + 12 * idx
    decreases |ac| - idx
  {
    LineCostBound(ac[idx]);
    SumLenSnoc(lines, FormatLenAndElems(ac[idx]));
    lines := lines + [FormatLenAndElems(ac[idx])];
    steps := steps + LineCost(ac[idx]) + 4;
    idx := idx + 1;
  }
  output := IntToString(|ac|) + "\n" + Join(lines, "\n");
  IntToStringDigits(|ac|);
  steps := steps + Digits(|ac|) + 1 + (SumLen(lines) + |lines|) + |Join(lines, "\n")| + 2;
  if |lines| >= 1 { JoinLen(lines, "\n"); }
  assert |Join(lines, "\n")| >= SumLen(lines);
  assert SumLen(lines) <= |output|;
  CostMulMonoLeft(it, n, K);
  assert n * K == 40 * (n * n) + 40 * n;
  assert |lines| <= |ac| <= it;
}
