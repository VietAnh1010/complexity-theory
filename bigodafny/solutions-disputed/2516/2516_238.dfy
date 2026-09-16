// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-19
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     Inside Go's while loop, b := b[i+1 := 1-b[i+1]] is a seq update
//     copying all |b|=n elements, and it can execute on up to n
//     iterations, giving O(n**2); Python's b[i+1] ^= 1 is an O(1) list
//     write so the Python stays O(n) as labeled.
//
//   how this label could be wrong, and what to check:
//     The label assumes each flip in Go is O(1) as in Python's b[i+1] ^=
//     1. Open the while loop in Go and confirm the line b := b[i+1 :=
//     1-b[i+1]] is a seq update; since this can fire on nearly every
//     iteration, check whether it runs close to n times, each copying
//     |b|=n elements, which would make this quadratic rather than linear.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 47, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "JoinInts"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 1,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": true, "set_build_in_loop": false, "sorts": [],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1271_B. Blocks  (problem 2516, solution 2516_238)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// a = input()
// 
// 
// def go(s, x):
//   b = [1 if c == 'B' else 0 for c in s]
//   o = []
//   n = len(b)
//   for i in range(n):
//     if b[i] != x:
//       if i + 1 >= n:
//         return 0
//       o += i + 1,
//       b[i + 1] = b[i + 1] ^ 1
//   print(len(o))
//   print(' '.join(map(str, o)))
//   return 1
// 
// 
// if not go(a, 0) and not go(a, 1):
//   print(-1)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Go(bIn: seq<int>, x: int) returns (ok: bool, out: string)
  requires forall k :: 0 <= k < |bIn| ==> bIn[k] == 0 || bIn[k] == 1
{
  var b := bIn;
  var n := |b|;
  var ops: seq<int> := [];
  var i := 0;
  var failed := false;
  while i < n && !failed
    invariant 0 <= i <= n
    invariant |b| == n
  {
    if b[i] != x {
      if i + 1 >= n {
        failed := true;
      } else {
        ops := ops + [i + 1];
        b := b[i + 1 := 1 - b[i + 1]];
      }
    }
    i := i + 1;
  }
  if failed {
    ok := false;
    out := "";
  } else {
    ok := true;
    out := IntToString(|ops|) + "\n" + JoinInts(ops, " ") + "\n";
  }
}

method Solve(n: int, is_white_list: seq<bool>) returns (output: string)
{
  var b := seq(|is_white_list|, i requires 0 <= i < |is_white_list| => if is_white_list[i] then 0 else 1);
  var ok0, out0 := Go(b, 0);
  if ok0 {
    output := out0;
  } else {
    var ok1, out1 := Go(b, 1);
    if ok1 {
      output := out1;
    } else {
      output := "-1\n";
    }
  }
}
