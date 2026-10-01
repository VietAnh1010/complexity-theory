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

method Solve(a: int, b_list: seq<int>) returns (output: string)
  requires |b_list| == a
{
  var n := a;
  var c: seq<int> := b_list;
  var ac: seq<seq<int>> := [];
  var f := if n % 2 == 1 then 1 else 0;
  var tar := n;
  while tar >= 1
    decreases tar
  {
    var split: seq<int> := [];
    var cnt := 0;
    if f == 1 {
      var i := 0;
      while i < |c|
        invariant 0 <= i <= |c|
        invariant cnt >= 0
        invariant SumInts(split) + cnt == i
        invariant forall t :: 0 <= t < |split| ==> split[t] >= 1
        decreases |c| - i
      {
        cnt := cnt + 1;
        if tar <= c[i] {
          SumIntsAppend(split, [cnt]);
          split := split + [cnt];
          cnt := 0;
        }
        i := i + 1;
      }
    } else {
      var i := |c| - 1;
      while i >= 0
        invariant -1 <= i <= |c| - 1
        invariant cnt >= 0
        invariant SumInts(split) + cnt == |c| - 1 - i
        invariant forall t :: 0 <= t < |split| ==> split[t] >= 1
        decreases i + 1
      {
        cnt := cnt + 1;
        if tar <= c[i] {
          SumIntsAppend(split, [cnt]);
          split := split + [cnt];
          cnt := 0;
        }
        i := i - 1;
      }
    }
    if cnt != 0 {
      SumIntsAppend(split, [cnt]);
      split := split + [cnt];
    }
    assert SumInts(split) == |c|;
    assert forall t :: 0 <= t < |split| ==> split[t] >= 1;
    if f == 0 {
      ghost var before := split;
      split := ReverseInt(split);
      SumIntsReverse(before);
      ReverseIntElems(before);
    }
    assert SumInts(split) == |c|;
    assert forall t :: 0 <= t < |split| ==> split[t] >= 1;
    if |split| == 1 {
      f := 1 - f;
    } else {
      ac := ac + [split];
      var segs: seq<seq<int>> := [];
      var s := 0;
      var k := 0;
      while k < |split|
        invariant 0 <= k <= |split|
        invariant 0 <= s <= |c|
        invariant s == SumInts(split[..k])
        decreases |split| - k
      {
        SplitPrefixSum(split, k);
        SplitPrefixBound(split, k);
        segs := segs + [c[s..s + split[k]]];
        s := s + split[k];
        k := k + 1;
      }
      var revSegs := ReverseListOfLists(segs);
      var newArr: seq<int> := [];
      var t := 0;
      while t < |revSegs|
        invariant 0 <= t <= |revSegs|
        decreases |revSegs| - t
      {
        newArr := newArr + revSegs[t];
        t := t + 1;
      }
      c := newArr;
      f := 1 - f;
    }
    tar := tar - 1;
  }
  var lines: seq<string> := [];
  var idx := 0;
  while idx < |ac|
    invariant 0 <= idx <= |ac|
    decreases |ac| - idx
  {
    lines := lines + [FormatLenAndElems(ac[idx])];
    idx := idx + 1;
  }
  output := IntToString(|ac|) + "\n" + Join(lines, "\n");
}
