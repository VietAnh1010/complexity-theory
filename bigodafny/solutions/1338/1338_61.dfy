// 1261_B1. Optimal Subsequences (Easy Version)  (problem 1338, solution 1338_61)
// time complexity: O(n*m)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import copy
// a=[]
// ai=[]
// otv=''
// n=int(input())
// a=list(map(int,input().split()))
// m=int(input())
// for i in range(1,m+1):
//     #print(ai)
//     #print(a,'kkkk')
//     ai=copy.deepcopy(a)
//     ai.reverse()
//     #print(ai)
//     k,pos=map(int,input().split())
//     for j in range(1,n-k+1):
//         #print(min(ai))
//         ai.remove(min(ai))
//     ai.reverse()
//     otv=otv+'\n'+str(ai[pos-1])
// print(otv)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ReverseSeq(s: seq<int>): seq<int>
  ensures |ReverseSeq(s)| == |s|
  decreases |s|
{
  if |s| == 0 then [] else ReverseSeq(s[1..]) + [s[0]]
}

function FindMinIndexFrom(s: seq<int>, i: int, best: int): int
  requires 0 <= best < |s|
  requires 0 <= i <= |s|
  ensures 0 <= FindMinIndexFrom(s, i, best) < |s|
  decreases |s| - i
{
  if i == |s| then best
  else if s[i] < s[best] then FindMinIndexFrom(s, i + 1, i)
  else FindMinIndexFrom(s, i + 1, best)
}

function FindMinIndex(s: seq<int>): int
  requires |s| > 0
  ensures 0 <= FindMinIndex(s) < |s|
{
  FindMinIndexFrom(s, 1, 0)
}

function RemoveAt(s: seq<int>, idx: int): seq<int>
  requires 0 <= idx < |s|
  ensures |RemoveAt(s, idx)| == |s| - 1
{
  s[..idx] + s[idx + 1..]
}

method Solve(n: int, a_list: seq<int>, q: int, queries: seq<(int, int)>) returns (output: string)
  requires n == |a_list|
  requires forall qq :: 0 <= qq < |queries| ==> 1 <= queries[qq].0 <= n
{
  var parts: seq<string> := [];
  var qi := 0;
  while qi < |queries|
    invariant 0 <= qi <= |queries|
    decreases |queries| - qi
  {
    var kk := queries[qi].0;
    var pos := queries[qi].1;
    var ai := ReverseSeq(a_list);
    var removeCount := if n - kk > 0 then n - kk else 0;
    var jcount := 0;
    while jcount < removeCount
      invariant 0 <= jcount <= removeCount
      invariant |ai| == n - jcount
      invariant removeCount <= n
      decreases removeCount - jcount
    {
      var mi := FindMinIndex(ai);
      ai := RemoveAt(ai, mi);
      jcount := jcount + 1;
    }
    ai := ReverseSeq(ai);
    if 0 <= pos - 1 < |ai| {
      parts := parts + ["\n" + IntToString(ai[pos - 1])];
    }
    qi := qi + 1;
  }
  output := Join(parts, "") + "\n";
}
