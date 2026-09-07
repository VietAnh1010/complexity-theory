// 1427_D. Unshuffling a Deck  (problem 1733, solution 1733_49)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// c=[*map(int,input().split())]
// if n%2:c=[n+1-i for i in c]
// q=0
// o=[]
// for i in range(n):
//     j=c.index(i+1)
//     m=[1]*i
//     if j-i+1:m.append(j-i+1)
//     m+=[1]*(n-1-j)
//     if i:c=c[:i]+c[j:i-1:-1]+c[j+1:]
//     else:c=c[:i]+c[j::-1]+c[j+1:]
//     if len(m)>1:
//         q+=1
//         if i%2:m=m[::-1]
//         m=[len(m)]+m
//         o.append(' '.join(map(str,m)))
// print(q)
// print('\n'.join(o))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function RepeatInt(v: int, cnt: int): seq<int>
  requires cnt >= 0
  ensures |RepeatInt(v, cnt)| == cnt
  decreases cnt
{
  if cnt == 0 then [] else [v] + RepeatInt(v, cnt - 1)
}

function ReverseInt(s: seq<int>): seq<int>
  ensures |ReverseInt(s)| == |s|
  decreases |s|
{
  if |s| == 0 then [] else ReverseInt(s[1..]) + [s[0]]
}

function IndexOfInt(s: seq<int>, v: int): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == v then 0
  else 1 + IndexOfInt(s[1..], v)
}

method Solve(a: int, b_list: seq<int>) returns (output: string)
  requires |b_list| == a
{
  var n := a;
  var c: seq<int> := b_list;
  if n % 2 == 1 {
    var nc: seq<int> := [];
    var k := 0;
    while k < |c|
      invariant 0 <= k <= |c|
      decreases |c| - k
    {
      nc := nc + [n + 1 - c[k]];
      k := k + 1;
    }
    c := nc;
  }
  var q := 0;
  var o: seq<string> := [];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    decreases n - i
  {
    var j := IndexOfInt(c, i + 1);
    var m: seq<int> := RepeatInt(1, i);
    if j - i + 1 != 0 {
      m := m + [j - i + 1];
    }
    var tail := n - 1 - j;
    var tailN := if tail < 0 then 0 else tail;
    m := m + RepeatInt(1, tailN);
    var mid := ReverseInt(c[i..j + 1]);
    c := c[..i] + mid + c[j + 1..];
    if |m| > 1 {
      q := q + 1;
      if i % 2 == 1 {
        m := ReverseInt(m);
      }
      m := [|m|] + m;
      o := o + [JoinInts(m, " ")];
    }
    i := i + 1;
  }
  output := IntToString(q) + "\n" + Join(o, "\n");
}
