// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-08
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     The first while loop over `cur` builds map `s` via `s := s[key :=
//     s[key]+1]` (or `s[key:=1]`) on every iteration, and each map write
//     is O(|s|) per the dataset's map-copy rule, giving O(n**2) total
//     across the O(n)-length loop; Python's dict assignment `s[key]=...`
//     is O(1) amortised so the Python is genuinely O(n).
//
//   how this label could be wrong, and what to check:
//     The label assumes the map `s` behaves like Python's dict with O(1)
//     amortised writes. Open the first while loop and check whether `s` is
//     updated via `s := s[key := s[key]+1]` (or `s[key:=1]`) inside the
//     loop; a map write copies the whole map per the O(|m|) rule, so if
//     this executes once per iteration of an O(n)-length loop the total is
//     O(n**2), not O(n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 61, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 3, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": true,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  // Python does p.index(k), which raises ValueError when k is absent, so this
  // excludes no input Python answers.
  requires exists c :: 0 <= c < n && a_list[c] == k
{
  var m := k;
  var p := a_list;
  var wIdx :| 0 <= wIdx < n && p[wIdx] == m;
  var cur := 0;
  while p[cur] != m
    invariant 0 <= cur <= wIdx
    decreases wIdx - cur
  {
    cur := cur + 1;
  }
  var pos := cur;
  var s: map<int, int> := map[];
  var cnt := 0;
  var length := 0;
  cur := pos;
  while cur >= 0
    invariant -1 <= cur <= pos
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
  }
  cur := pos;
  cnt := 0;
  length := 0;
  var ans := 0;
  while cur < n
    invariant pos <= cur <= n
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
  }
  output := IntToString(ans) + "\n";
}
