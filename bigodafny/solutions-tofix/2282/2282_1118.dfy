// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-17
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     BuildMaxDigits1118(m,s) returns "9" + BuildMaxDigits1118(m-1, s-9)
//     (and BuildMinDigits1118 the analogous [9] + recurse(...)),
//     concatenating at every one of m recursion levels rather than in an
//     iterative accumulator loop, costing Theta(m**2); Python's
//     ismax/ismin instead use an iterative op1=op1+'9' loop, which is
//     CPython's amortized-O(1) string concat idiom, so the Python stays
//     O(m) plus the O(m log m) sorted(lis) in ismin.
//
//   how this label could be wrong, and what to check:
//     The label assumes the digit-building cost stays linear as in
//     Python's for-i-in-range(m) loop with op1=op1+'9'. But
//     BuildMaxDigits1118/BuildMinDigits1118 are recursive functions that
//     concatenate a literal onto the recursive call's result at every one
//     of m levels -- the same 'concatenates at every level' shape flagged
//     for 888_6 in this prompt, which is O(n**2), not the O(1)-per-append
//     deferred-concat loop case. Confirm by counting: each level's concat
//     costs O(remaining recursion depth), summing to O(m**2).
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 51, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "JoinInts"],
//     "loop_depth": 0, "loops": 0, "recursive_helpers": 2,
//     "seq_append_read_in_same_loop": false, "seq_args": 0,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["SortInts"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 489_C. Given Length and Sum of Digits...  (problem 2282, solution 2282_1118)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// m,s=map(int,input().split())
//  
// def ismax(m,s):
//     op1=str()
//     if s==0:
//         return(-1)
//     elif s>m*9:
//         return(-1)
//     else:
//         for i in range(m):
//             if s>9:
//                 op1=op1+'9'
//                 s-=9
//             elif 0<s<=9:
//                 op1=op1+str(s)
//                 s=0
//             else:
//                 op1=op1+'0'
//         return(int(op1))
// 
// def ismin(m,s):
//     op2=str()
//     lis=[]
//     if s==0:
//         return(-1)
//     elif s>m*9:
//         return(-1)
//     else:
//         l=max(1,s-9*(m-1))
//         op2=op2+str(l)
//         s=s-l
//         for i in range(m-1):
//             if s>9:
//                 lis.append(9)
//                 s-=9
//             elif 0<s<=9:
//                 lis.append(s)
//                 s=0
//             else:
//                 lis.append(0)
//         lis=sorted(lis)
//         if len(lis)==1:
//             op2=op2+str(*lis)
//         elif len(lis)>1:
//             st="".join(map(str,lis))
//             op2=op2+st
//         return(int(op2))
// if m==1 and s==0:
//     print(0, 0)
// else:
//     print(ismin(m,s),ismax(m,s))
//     
//                 
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int) returns (output: string)
  requires n >= 0
{
  var m := n;
  var s := k;
  if m == 1 && s == 0 {
    output := "0 0";
  } else {
    var mn := IsMin1118(m, s);
    var mx := IsMax1118(m, s);
    output := mn + " " + mx;
  }
}

function IsMax1118(m: int, s: int): string
  requires m >= 0
{
  if s == 0 then "-1"
  else if s > m * 9 then "-1"
  else BuildMaxDigits1118(m, s)
}

function BuildMaxDigits1118(m: int, s: int): string
  decreases if m > 0 then m else 0
{
  if m <= 0 then ""
  else if s > 9 then "9" + BuildMaxDigits1118(m - 1, s - 9)
  else if 0 < s && s <= 9 then IntToString(s) + BuildMaxDigits1118(m - 1, 0)
  else "0" + BuildMaxDigits1118(m - 1, s)
}

function IsMin1118(m: int, s: int): string
  requires m >= 0
{
  if s == 0 then "-1"
  else if s > m * 9 then "-1"
  else
    var l := if 1 > s - 9 * (m - 1) then 1 else s - 9 * (m - 1);
    IntToString(l) + BuildMinDigitsSorted1118(BuildMinDigits1118(m - 1, s - l))
}

function BuildMinDigits1118(m: int, s: int): seq<int>
  decreases if m > 0 then m else 0
{
  if m <= 0 then []
  else if s > 9 then [9] + BuildMinDigits1118(m - 1, s - 9)
  else if 0 < s && s <= 9 then [s] + BuildMinDigits1118(m - 1, 0)
  else [0] + BuildMinDigits1118(m - 1, s)
}

function BuildMinDigitsSorted1118(lis: seq<int>): string
{
  JoinInts(SortInts(lis), "")
}
