// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-10
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The outer loop runs h times and the inner loop plus the seq(w + 2, _
//     => 0) allocation cost O(w) per outer iteration, so the cost is
//     O(h*w) in two input values; the Python list comprehension over
//     range(1, w+1) pays the same, and the statement cap W<=8 is not a
//     source literal.
//
//   how this label could be wrong, and what to check:
//     The label treats a single variable as the size, but the cost is the
//     product of two input values h and w. Check the nested loops: the
//     outer runs while i < h and the inner while j <= w, with seq(w + 2,
//     ...) allocated per outer iteration; if w were fixed by a source
//     literal the label would stand, but only a requires clause caps it.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 34, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p03222 AtCoder Beginner Contest 113 - Number of Amidakuji  (problem 1861, solution 1861_16)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// f=[0,1,1,2,3,5,8,13,21,34,55,89];h,w,k=map(int,input().split());a=[0]*(w+2);a[1]=1
// for i in range(h):a=[0]+[(f[j-1]*f[w-j+1]*a[j-1]+f[j]*f[w-j+1]*a[j]+f[j]*f[w-j]*a[j+1])%(10**9+7)for j in range(1,w+1)]+[0]
// print(a[k])
// --------------------------------------------------------------------

include "../../../prelude.dfy"

method Solve(a: int, b: int, c: int)
    returns (output: string, ghost steps: nat)
  requires a >= 1
  requires 1 <= b <= 11
  requires 0 <= c <= b + 1
  ensures steps <= 18 + b + a * (7 + 31 * b) + |output|
{
  steps := 0;
  var h := a;
  var w := b;
  var k := c;
  steps := steps + 12;
  var f := [0, 1, 1, 2, 3, 5, 8, 13, 21, 34, 55, 89];
  var MOD := 1000000007;
  steps := steps + (1 + (w + 2));
  var arr := seq(w + 2, _ /* _v0 */ => 0);
  steps := steps + 1;
  arr := arr[1 := 1];
  ghost var K: nat := 7 + 31 * w;
  var i := 0;
  while i < h
    invariant 0 <= i <= h
    invariant |arr| == w + 2
    invariant steps <= 16 + w + i * K
    decreases h - i
  {
    ghost var s0 := steps;
    steps := steps + 2;
    steps := steps + (1 + (w + 2));
    var newArr := seq(w + 2, _ /* _v1 */ => 0);
    var j := 1;
    ghost var s1 := steps;
    while j <= w
      invariant 1 <= j <= w + 1
      invariant |newArr| == w + 2
      invariant steps <= s1 + 30 * (j - 1)
      decreases w - j + 1
    {
      steps := steps + 2;
      steps := steps + 26;
      var val := (f[j - 1] * f[w - j + 1] * arr[j - 1] + f[j] * f[w - j + 1] * arr[j] + f[j] * f[w - j] * arr[j + 1]) % MOD;
      steps := steps + 1;
      newArr := newArr[j := val];
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + 1;
    arr := newArr;
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, K);
    i := i + 1;
  }
  steps := steps + 1;
  steps := steps + (1 + Digits(arr[k]));
  IntToStringDigits(arr[k]);
  output := IntToString(arr[k]);
}

import opened Prelude
