// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Both the Python loops and the Dafny loop read only
//     `coordinates[i][0]` and `coordinates[i][1]` of each of the n rows
//     and insert into sets, so the cost is O(n); a row is a fixed
//     two-number pair, never walked.
//
//   how this label could be wrong, and what to check:
//     The label assumes row width varies. Each row is an alarm clock's (x,
//     y) pair, and both the Python and the Dafny read only `[0]` and
//     `[1]`. Check the problem's input format: if every line has exactly
//     two numbers, m is constant and the class is O(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 21, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": true, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": true}
// --------------------------------------------------------------------

// 390_A. Inna and Alarm Clock  (problem 225, solution 225_145)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// d1={}
// d2={}
// n=int(input())
// l=[]
// for i in range(n):
//     x=list(map(int,input().split()))
//     l.append(x)
// for i in range(n):
//     if(l[i][0] not in d1):
//         d1[l[i][0]]=1
// sum1=sum(d1.values())
// for i in range(n):
//     if(l[i][1] not in d2):
//         d2[l[i][1]]=1
// sum2=sum(d2.values())
// print(sum1) if(sum1<=sum2) else print(sum2)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, coordinates: seq<seq<int>>) returns (output: string, ghost steps: nat)
  requires n <= |coordinates|
  requires forall k :: 0 <= k < |coordinates| ==> |coordinates[k]| >= 2
  ensures steps <= 12 * (if n > 0 then n else 0) + 2 * |output| + 10
{
  steps := 1;
  var xs: set<int> := {};
  var ys: set<int> := {};
  var i := 0;
  while i < n
    invariant 0 <= i
    invariant i <= n || i == 0
    invariant steps <= 1 + 12 * i
    decreases n - i
  {
    xs := xs + {coordinates[i][0]};
    ys := ys + {coordinates[i][1]};
    i := i + 1;
    steps := steps + 12;
  }
  var sx := |xs|;
  var sy := |ys|;
  ghost var r := if sx <= sy then sx else sy;
  output := IntToString(if sx <= sy then sx else sy);
  IntToStringDigits(r);
  steps := steps + 4 + Digits(r);
}
