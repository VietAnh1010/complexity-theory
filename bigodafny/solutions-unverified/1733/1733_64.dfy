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
        decreases |c| - i
      {
        cnt := cnt + 1;
        if tar <= c[i] {
          split := split + [cnt];
          cnt := 0;
        }
        i := i + 1;
      }
    } else {
      var i := |c| - 1;
      while i >= 0
        decreases i + 1
      {
        cnt := cnt + 1;
        if tar <= c[i] {
          split := split + [cnt];
          cnt := 0;
        }
        i := i - 1;
      }
    }
    if cnt != 0 {
      split := split + [cnt];
    }
    if f == 0 {
      split := ReverseInt(split);
    }
    if |split| == 1 {
      f := 1 - f;
    } else {
      ac := ac + [split];
      var segs: seq<seq<int>> := [];
      var s := 0;
      var k := 0;
      while k < |split|
        invariant 0 <= k <= |split|
        decreases |split| - k
      {
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
