// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve concatenates the two pieces, scans `rest` once for '=', runs
//     CountChar three times over the pieces and builds at most one result
//     with RepStr counts bounded by the expression length, so every step
//     is linear in the input text: O(n). The Python does one `for i in s`
//     pass and a few slices, so it is O(n) as well and the label is wrong;
//     the input arrives as two strings, so O(n+m) is the other reading.
//
//   how this label could be wrong, and what to check:
//     The label claims quadratic work on what looks like a few passes.
//     Check CountChar (linear recursion on the string) and RepStr
//     (recursion on a count bounded by the string length): none is nested
//     inside another loop over the same size.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 62, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 2, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 394_A. Counting Sticks  (problem 2799, solution 2799_66)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=input()
// ar=[0,0,0]
// k=0
// for i in s:
//     if i=='|':
//         ar[k]+=1
//     else:
//         k+=1
// if ar[0]+ar[1]-ar[2]==0:
//     print(s)
// elif ar[0]+ar[1]-ar[2]==2:
//     if ar[0]>1:
//         print(s[1:]+s[0])
//     else:
//         s='|'*ar[0]+"+"+'|'*(ar[1]-1)+"="+'|'*(ar[2]+1)
//         print(s)
// elif ar[0]+ar[1]-ar[2]==-2:
//     if ar[2]>1:
//         print(s[-1]+s[0:len(s)-1])
//     else:
//         s='|'*ar[0]+"+"+'|'*(ar[1]+1)+"="+'|'*(ar[2]-1)
// else:
//     print("Impossible")
// 
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CountChar(s: string, c: char): int
{
  if |s| == 0 then 0
  else (if s[0] == c then 1 else 0) + CountChar(s[1..], c)
}

function RepStr(s: string, n: int): string
  decreases if n > 0 then n else 0
{
  if n <= 0 then "" else s + RepStr(s, n - 1)
}

method Solve(v_0: seq<string>) returns (output: string)
{
  if |v_0| < 2 {
    output := "";
    return;
  }
  var s := v_0[0] + "+" + v_0[1];
  var l0 := v_0[0];
  var rest := v_0[1];
  var eqIdx := 0;
  var found := false;
  var t := 0;
  while t < |rest|
    invariant 0 <= t <= |rest|
    invariant found ==> 0 <= eqIdx < |rest|
  {
    if !found && rest[t] == '=' {
      eqIdx := t;
      found := true;
    }
    t := t + 1;
  }
  var l1 := if found then rest[..eqIdx] else rest;
  var l2 := if found then rest[eqIdx+1..] else "";

  var a0 := CountChar(l0, '|');
  var a1 := CountChar(l1, '|');
  var a2 := CountChar(l2, '|');
  var result := (a0 + a1) - a2;
  if result == 0 {
    output := s;
  } else if result == 2 {
    if a0 > 1 {
      var tail := if |s| > 0 then [s[0]] else "";
      var head := if |s| > 0 then s[1..] else "";
      output := head + tail;
    } else {
      output := RepStr("|", a0) + "+" + RepStr("|", a1 - 1) + "=" + RepStr("|", a2 + 1);
    }
  } else if result == -2 {
    if a2 > 1 {
      var last := if |s| > 0 then [s[|s|-1]] else "";
      var head := if |s| > 0 then s[0..|s|-1] else "";
      output := last + head;
    } else {
      output := "";
    }
  } else {
    output := "Impossible";
  }
}
