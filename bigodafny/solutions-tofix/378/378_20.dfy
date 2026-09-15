// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r2-02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both loops touch only pairs[idx][0] and pairs[idx][1] via ParseInt
//     -- no dimension beyond n=|pairs| is scanned -- and map<int,int>
//     lookups/inserts are the only other cost, which the table marks
//     UNMEASURED rather than tied to any m. Sibling 378_91 solves the same
//     problem (432_B Football Kit) with an isomorphic
//     ParseInt+map<int,int> two-loop structure and carries label O(n), so
//     this row's extra 'm' factor is not visible anywhere in the Dafny.
//
//   how this label could be wrong, and what to check:
//     The label claims a second dimension m (row width, or the
//     digit-length of the team-id strings parsed by ParseInt) drives the
//     cost, but both loops only ever touch pairs[idx][0] and pairs[idx][1]
//     -- no width or length beyond n=|pairs| is scanned -- and
//     map<int,int> lookups/inserts (the only other cost) are UNMEASURED in
//     this cost model. Check whether team/kit indices in problem 432_B are
//     bounded by n (then any string round-trip via ParseInt is O(log n),
//     not an independent m); also diff this Dafny against sibling 378_91,
//     which has an isomorphic ParseInt+map<int,int> two-loop structure for
//     the same problem and carries label O(n) -- if the structures really
//     are equivalent, this row's extra m factor is a stale label rather
//     than a real cost.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 48, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "ParseInt",
//     "ParseIntFrom"], "loop_depth": 1, "loops": 2, "recursive_helpers":
//     2, "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": true, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 432_B. Football Kit  (problem 378, solution 378_20)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// x=[]
// for i in range(n):
//     x.append(list(map(int,input().split())))
//  
// h={}
// a={}
// for i in range(n):
//     if(h.get(str(x[i][0]))):
//         h[str(x[i][0])]+=1
//     else:
//         h[str(x[i][0])]=1
//     
// for i in range(n):
//     home=n-1
//     if(h.get(str(x[i][1]))):
//         if(h[str(x[i][1])]>0):
//             away= n-1-h[str(x[i][1])]
//             home+=h[str(x[i][1])]
//     else:
//         away=n-1
//     print(home,away)   
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string)
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
{
  var h: map<int, int> := map[];
  var idx := 0;
  while idx < |pairs|
    decreases |pairs| - idx
  {
    var home0 := ParseInt(pairs[idx][0]);
    if home0 in h {
      h := h[home0 := h[home0] + 1];
    } else {
      h := h[home0 := 1];
    }
    idx := idx + 1;
  }
  var lines: seq<string> := [];
  idx := 0;
  while idx < |pairs|
    decreases |pairs| - idx
  {
    var away0 := ParseInt(pairs[idx][1]);
    var home := n - 1;
    var away := n - 1;
    if away0 in h {
      var cnt := h[away0];
      away := n - 1 - cnt;
      home := home + cnt;
    }
    lines := lines + [IntToString(home) + " " + IntToString(away)];
    idx := idx + 1;
  }
  output := Join(lines, "\n");
}
