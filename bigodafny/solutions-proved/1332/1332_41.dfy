// 1005_E1. Median on Segments (Permutations Edition)  (problem 1332, solution 1332_41)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,m=map(int,input().split())
// p=list(map(int,input().split()))
// cur=0
// while p[cur]!=m:
//     cur+=1
// pos=cur
// s={}
// cnt,len=0,0
// while cur>=0:
//     if p[cur]<=m:
//         cnt+=1
//     len+=1
//     if 2*cnt-len in s:
//         s[2*cnt-len]+=1
//     else:
//         s[2*cnt-len]=1
//     cur-=1
// cur=pos
// cnt,len,ans=0,0,0
// while cur<n:
//     if p[cur]<=m:
//         cnt+=1
//     len+=1
//     if len-2*cnt+1 in s:
//         ans+=s[len-2*cnt+1]
//     if len-2*cnt+2 in s:
//         ans+=s[len-2*cnt+2]
//     cur+=1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  // Python does p.index(k), which raises ValueError when k is absent, so this
  // excludes no input Python answers.
  requires exists c :: 0 <= c < n && a_list[c] == k
  ensures steps <= 12 * |a_list| + 12
{
  steps := 1;
  var m := k;
  var p := a_list;
  var wIdx :| 0 <= wIdx < n && p[wIdx] == m;
  var cur := 0;
  while p[cur] != m
    invariant 0 <= cur <= wIdx
    invariant steps <= 1 + 2 * cur
    decreases wIdx - cur
  {
    cur := cur + 1;
    steps := steps + 2;
  }
  var pos := cur;
  var s: map<int, int> := map[];
  var cnt := 0;
  var length := 0;
  cur := pos;
  ghost var loop1start := steps;
  while cur >= 0
    invariant -1 <= cur <= pos
    invariant steps <= loop1start + 6 * (pos - cur)
    decreases cur + 1
  {
    if p[cur] <= m {
      cnt := cnt + 1;
    }
    length := length + 1;
    var key := 2 * cnt - length;
    if key in s {
      s := s[key := s[key] + 1];
    } else {
      s := s[key := 1];
    }
    cur := cur - 1;
    steps := steps + 6;
  }
  cur := pos;
  cnt := 0;
  length := 0;
  var ans := 0;
  ghost var loop2start := steps;
  while cur < n
    invariant pos <= cur <= n
    invariant steps <= loop2start + 8 * (cur - pos)
    decreases n - cur
  {
    if p[cur] <= m {
      cnt := cnt + 1;
    }
    length := length + 1;
    var k1 := length - 2 * cnt + 1;
    var k2 := length - 2 * cnt + 2;
    if k1 in s {
      ans := ans + s[k1];
    }
    if k2 in s {
      ans := ans + s[k2];
    }
    cur := cur + 1;
    steps := steps + 8;
  }
  output := IntToString(ans) + "\n";
  steps := steps + 2;
}
