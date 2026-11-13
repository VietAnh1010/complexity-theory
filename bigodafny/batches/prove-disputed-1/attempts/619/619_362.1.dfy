// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : both
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     The Python builds each signature in O(26 + |x|) and inserts into the
//     set `ss`, O(n*m) overall; the Dafny adds an O(n**2)
//     linear-membership pass in `CountDistinct619b` over seq `seen`, so it
//     is O(n*m + n**2).
//
//   how this label could be wrong, and what to check:
//     The Python scans each of n words once and adds its signature to a
//     set, O(n*m) for words of length m, so `O(n**2)` squares the wrong
//     size. The Dafny's `CountDistinct619b` keeps `seen` as a seq and
//     scans it per word, O(n**2) for distinct roots. Check the type of
//     `seen` against the Python's `set()`.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 58, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 4, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 975_A. Aramic script  (problem 619, solution 619_362)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// t=str(input()) 
// arr = [str(x) for x in input().split()]
// 
// 
// ss = set()
// 
// for x in arr:
//       a2 = []
//       s=""
//       for i in range(int(26)):
//               a2.append(0)
//       for i in range(len(x)):
//               nu = ord(x[i]) 
//               nu = nu - ord('a')
//               a2[nu]=1 
//       for i in range(int(26)): 
//             if a2[i]==1:
//                 s=s+str(chr(i +ord('a'))) 
//       ss.add(s) 
// 
// 
// print(len(ss))
//       
//        
//      
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 330 * |strings| + 8 * SumLen(strings) + 30 * |strings| * |strings| + |output| + 10
{
  steps := 1;
  var sigs: seq<string> := [];
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    invariant |sigs| == i
    invariant forall j :: 0 <= j < i ==> |sigs[j]| <= 26
    invariant steps <= 1 + 330 * i + 8 * SumLen(strings[..i])
    decreases |strings| - i
  {
    var sg, st := Signature619b(strings[i]);
    sigs := sigs + [sg];
    assert strings[..i + 1] == strings[..i] + [strings[i]];
    SumLenSnoc(strings[..i], strings[i]);
    steps := steps + st + 4;
    i := i + 1;
  }
  assert strings[..|strings|] == strings;
  var distinctCount, st2 := CountDistinct619b(sigs);
  CostMulMono(|strings|, |strings|, |strings|);
  steps := steps + st2;
  output := IntToString(distinctCount);
  IntToStringDigits(distinctCount);
  steps := steps + Digits(distinctCount);
}

method Signature619b(s: string) returns (sig: string, ghost steps: nat)
  ensures |sig| <= 26
  ensures steps <= 8 * |s| + 300
{
  steps := 30;
  var pres := seq(26, _ => false);
  var i := 0;
  while i < |s|
    invariant |pres| == 26
    invariant 0 <= i <= |s|
    invariant steps == 30 + 8 * i
    decreases |s| - i
  {
    var idx := (s[i] as int) - ('a' as int);
    if 0 <= idx < 26 {
      pres := pres[idx := true];
    }
    i := i + 1;
    steps := steps + 8;
  }
  var alphabet := "abcdefghijklmnopqrstuvwxyz";
  sig := "";
  ghost var b := steps;
  i := 0;
  while i < 26
    invariant 0 <= i <= 26
    invariant |pres| == 26
    invariant |sig| <= i
    invariant steps == b + 8 * i
    decreases 26 - i
  {
    if pres[i] {
      sig := sig + [alphabet[i]];
    }
    i := i + 1;
    steps := steps + 8;
  }
}

method CountDistinct619b(xs: seq<string>) returns (c: int, ghost steps: nat)
  ensures (forall x :: x in xs ==> |x| <= 26) ==> steps <= 30 * |xs| * |xs| + 2
{
  steps := 1;
  var seen: seq<string> := [];
  var i := 0;
  ghost var K: nat := 4 + 27 * |xs|;
  while i < |xs|
    invariant 0 <= i <= |xs|
    invariant |seen| <= i
    invariant (forall x :: x in xs ==> |x| <= 26) ==> steps <= 1 + i * K
    decreases |xs| - i
  {
    if (forall x :: x in xs ==> |x| <= 26) {
      CostMulMonoLeft(|seen|, |xs|, 27);
      CostMulDistrib(i, 1, i + 1, K);
    }
    ghost var cost := 4 + 27 * |seen|;
    if xs[i] !in seen {
      seen := seen + [xs[i]];
    }
    i := i + 1;
    steps := steps + cost;
  }
  c := |seen|;
  if (forall x :: x in xs ==> |x| <= 26) {
    CostMulMono(|xs|, 4 + 27 * |xs|, 31 * |xs| + 0);
    assert |xs| <= |xs| * |xs| || |xs| == 0;
  }
}
