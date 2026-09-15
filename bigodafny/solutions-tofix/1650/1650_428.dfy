// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-11
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loop reads only pairs[i][0] and pairs[i][1] at fixed
//     positions, never a variable-length row, and the Python's
//     d[i][0]/d[i][1] access matches exactly, so both languages are O(n),
//     not O(n*m).
//
//   how this label could be wrong, and what to check:
//     The label assumes a variable row width m, but the description fixes
//     each line to exactly li and ri. Check the input format: if every
//     pairs[k] has length 2, no m dimension exists in either the Python
//     (d[i][0]/d[i][1]) or the Dafny (pairs[i][0]/pairs[i][1]), and the
//     true cost is O(n).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 20, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 248_A. Cupboards  (problem 1650, solution 1650_428)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #!/usr/bin/env python3
// # -*- coding: utf-8 -*-
// n=int(input())
// d=[]
// l,p,t=0,0,0,
// for i in range(n):
//     d.append(list(map(int,input().split())))
//     if d[i][0]==1:
//         l+=1
//     if d[i][1]==1:
//         p+=1
// if l<n-l:
//     t+=l
// else:
//     t+=n-l
// if p<n-p:
//     t+=p
// else:
//     t+=n-p
// print(t)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<seq<string>>) returns (output: string)
  // each line of input is a pair of tokens
  requires forall k :: 0 <= k < |pairs| ==> |pairs[k]| >= 2
{
  var l := 0;
  var p := 0;
  var i := 0;
  while i < |pairs|
    invariant 0 <= i <= |pairs|
    decreases |pairs| - i
  {
    if pairs[i][0] == "1" { l := l + 1; }
    if pairs[i][1] == "1" { p := p + 1; }
    i := i + 1;
  }
  var t1 := if l < n - l then l else n - l;
  var t2 := if p < n - p then p else n - p;
  output := IntToString(t1 + t2);
}
