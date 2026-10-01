// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : other
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r3d-04
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each query does ReverseSeq (O(n)) and then n-k iterations of
//     FindMinIndex (O(n) scan) plus RemoveAt (concat of O(n)), so one
//     query costs O(n*(n-k)) and the total is O(m*n**2), cubic when m is
//     about n; the Python's ai.remove(min(ai)) in `for j in
//     range(1,n-k+1)` pays O(n) twice per removal as well.
//
//   how this label could be wrong, and what to check:
//     The label gives n*m but the body has a removal loop nested inside
//     the query loop. Open the inner `while jcount < removeCount` loop:
//     removeCount = n - kk and each iteration runs FindMinIndex over all
//     of ai, so each query is about n**2 for small k; compare the Python's
//     `ai.remove(min(ai))` under `for j in range(1,n-k+1)`.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 63, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 4,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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
