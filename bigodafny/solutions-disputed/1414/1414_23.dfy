// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-s02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over the |strings| test cases and calls
//     Helper(strings[i]), which runs HelperPass1 and HelperPass2, each a
//     linear pass over that string, so the cost is n strings each scanned
//     once, O(n*m), not one size squared. The Python's helper(s) does the
//     same two passes per string, so the label is wrong for both.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) names one size squared, but the loops range over
//     two different sizes: the count of test strings and the length of
//     each string. Open Solve and Helper and check that the outer loop is
//     over |strings| and the passes are over |s| of each; if the strings
//     have independent lengths from the count (here up to 50 characters,
//     capped), the label should be O(n*m).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 87, "data_dependent_loops": 2, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     3, "recursive_helpers": 3, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 1494_A. ABC String  (problem 1414, solution 1414_23)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def STR(): return list(input())
// def INT(): return int(input())
// def MAP(): return map(int, input().split())
// def MAP2():return map(float,input().split())
// def LIST(): return list(map(int, input().split()))
// def STRING(): return input()
// import string
// import sys
// from heapq import heappop , heappush, heapify
// from bisect import *
// from collections import deque , Counter , defaultdict
// from math import *
// from itertools import permutations , accumulate
// dx = [-1 , 1 , 0 , 0  ]
// dy = [0 , 0  , 1  , - 1]
// 
// 
// def helper(s):
//     if s[0]==s[-1]:
//         print('NO')
//         return
//     a=[]
//     start=s[0]
//     end=s[-1]
//     flag=0
//     for i in s:
//         if i==start:
//             a.append('(')
//         elif i==end:
//             if len(a)==0:
//                 flag=1
//                 break
//             a.pop()
//         else:
//             a.append('(')
//     if len(a)==0 and flag==0:
//         print('YES')
//         return
//     a=[]
//     for i in s:
//         if i==s[0]:
//             a.append('(')
//         elif i==end:
//             if len(a)==0:
//                 print('NO')
//                 return
//             a.pop()
//         else:
//             if len(a)==0:
//                 print('NO')
//                 return
//             a.pop()
//     if len(a)==0:
//         print('YES')
//     else:
//         print("NO")
// 
// 
// for tt in range(INT()):
//     s=STRING()
//     helper(s)
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method HelperPass1(s: string, start: char, end: char) returns (stackLen: int, flag: bool)
{
  stackLen := 0;
  flag := false;
  var idx := 0;
  while idx < |s| && !flag
    invariant 0 <= idx <= |s|
    invariant stackLen >= 0
    decreases |s| - idx
  {
    var c := s[idx];
    if c == start {
      stackLen := stackLen + 1;
    } else if c == end {
      if stackLen == 0 {
        flag := true;
      } else {
        stackLen := stackLen - 1;
      }
    } else {
      stackLen := stackLen + 1;
    }
    idx := idx + 1;
  }
}

method HelperPass2(s: string, start: char, end: char) returns (result: string)
{
  var stackLen := 0;
  var idx := 0;
  var failed := false;
  while idx < |s| && !failed
    invariant 0 <= idx <= |s|
    invariant stackLen >= 0
    decreases |s| - idx
  {
    var c := s[idx];
    if c == start {
      stackLen := stackLen + 1;
    } else if c == end {
      if stackLen == 0 { failed := true; } else { stackLen := stackLen - 1; }
    } else {
      if stackLen == 0 { failed := true; } else { stackLen := stackLen - 1; }
    }
    idx := idx + 1;
  }
  if failed {
    result := "NO\n";
  } else if stackLen == 0 {
    result := "YES\n";
  } else {
    result := "NO\n";
  }
}

method Helper(s: string) returns (result: string)
  requires |s| > 0
{
  if s[0] == s[|s| - 1] {
    result := "NO\n";
  } else {
    var start := s[0];
    var end := s[|s| - 1];
    var stackLen, flag := HelperPass1(s, start, end);
    if stackLen == 0 && !flag {
      result := "YES\n";
    } else {
      result := HelperPass2(s, start, end);
    }
  }
}

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    decreases |strings| - i
  {
    if |strings[i]| > 0 {
      var r := Helper(strings[i]);
      parts := parts + [r];
    }
    i := i + 1;
  }
  output := Join(parts, "");
}
