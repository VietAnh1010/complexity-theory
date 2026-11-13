// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-08
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The inner `while j < a_list[i]` loops, the b/c array fills, and
//     JoinInts/sequence equality cost O(sum of a_i) on top of the O(n)
//     outer loops, so the real class is O(n + sum a_i), a value term. The
//     Python's `for j in range(a[i])` with b.append and `b == c` pays the
//     same, so the label is at fault, not the translation.
//
//   how this label could be wrong, and what to check:
//     The label assumes the cost is a product of two input sizes. Check
//     the loops over a_list[i]: the inner whiles run a_list[i] times, so
//     total cost is O(h + sum a_i), a cost in the element values the label
//     does not name; if m is meant as max a_i the label is only a loose
//     upper bound.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 85, "data_dependent_loops": 3, "decreases_star":
//     false, "linear_prelude_calls": ["JoinInts"], "loop_depth": 2,
//     "loops": 7, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 901_A. Hashing Trees  (problem 2723, solution 2723_27)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// *a, = map(int, input().split())
// b, c = [0], [0]
// cur = 1
// for i in range(1, n + 1):
//     for j in range(a[i]):
//         b.append(cur)
//     cur += a[i]
// cur = 1
// for i in range(1, n + 1):
//     if a[i] > 1 and a[i - 1] > 1:
//         c.append(cur - 1)
//         for j in range(1, a[i]):
//             c.append(cur)
//     else:
//         for j in range(a[i]):
//             c.append(cur)
//     cur += a[i]
// if b == c:
//     exit(print('perfect'))
// print('ambiguous')
// print(*b)
// print(*c)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

ghost function Pos(x: int): nat { if x > 0 then x else 0 }

ghost function SumNN(a: seq<int>, i: nat): nat
  requires i <= |a|
  decreases i
{
  if i <= 1 then 0 else SumNN(a, i - 1) + Pos(a[i - 1])
}

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| == n + 1
  requires n >= 0
  ensures steps <= 40 * n + 20 * SumNN(a_list, n + 1) + 30 + 2 * |output|
{
  steps := 5;
  var lenB := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant lenB <= 1 + SumNN(a_list, i)
    invariant steps <= 5 + 5 * (i - 1)
  {
    lenB := lenB + a_list[i];
    i := i + 1;
    steps := steps + 5;
  }
  var lenC := 1;
  i := 1;
  ghost var baseL2 := steps;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant lenC <= 1 + SumNN(a_list, i)
    invariant steps <= baseL2 + 5 * (i - 1)
  {
    lenC := lenC + a_list[i];
    i := i + 1;
    steps := steps + 5;
  }
  if lenB < 1 { lenB := 1; }
  if lenC < 1 { lenC := 1; }
  steps := steps + 4;
  assert lenB <= 1 + SumNN(a_list, n + 1);
  assert lenC <= 1 + SumNN(a_list, n + 1);
  ghost var W := SumNN(a_list, n + 1);

  var bArr := new int[lenB];
  steps := steps + lenB;
  bArr[0] := 0;
  var pos := 1;
  var cur := 1;
  i := 1;
  ghost var baseB := steps;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant steps <= baseB + 8 * (i - 1) + 6 * SumNN(a_list, i)
  {
    var j := 0;
    ghost var baseJ := steps;
    steps := steps + 8;
    while j < a_list[i]
      invariant 0 <= j <= Pos(a_list[i])
      invariant steps <= baseJ + 8 + 6 * j
    {
      if pos < lenB {
        bArr[pos] := cur;
      }
      pos := pos + 1;
      j := j + 1;
      steps := steps + 6;
    }
    cur := cur + a_list[i];
    i := i + 1;
  }

  var cArr := new int[lenC];
  steps := steps + lenC;
  cArr[0] := 0;
  pos := 1;
  cur := 1;
  i := 1;
  ghost var baseC := steps;
  while i <= n
    invariant 1 <= i <= n + 1
    invariant steps <= baseC + 12 * (i - 1) + 6 * SumNN(a_list, i)
  {
    ghost var baseJ := steps;
    steps := steps + 12;
    if a_list[i] > 1 && a_list[i - 1] > 1 {
      if pos < lenC { cArr[pos] := cur - 1; }
      pos := pos + 1;
      var j := 1;
      while j < a_list[i]
        invariant 1 <= j <= Pos(a_list[i])
        invariant steps <= baseJ + 12 + 6 * j
      {
        if pos < lenC { cArr[pos] := cur; }
        pos := pos + 1;
        j := j + 1;
        steps := steps + 6;
      }
    } else {
      var j := 0;
      while j < a_list[i]
        invariant 0 <= j <= Pos(a_list[i])
        invariant steps <= baseJ + 12 + 6 * j
      {
        if pos < lenC { cArr[pos] := cur; }
        pos := pos + 1;
        j := j + 1;
        steps := steps + 6;
      }
    }
    cur := cur + a_list[i];
    i := i + 1;
  }

  var bSeq := bArr[..];
  var cSeq := cArr[..];
  steps := steps + 3 * (1 + W) + 3;
  if bSeq == cSeq {
    output := "perfect\n";
  } else {
    output := "ambiguous\n" + JoinInts(bSeq, " ") + "\n" + JoinInts(cSeq, " ") + "\n";
    JoinIntsLen(bSeq, " ");
    JoinIntsLen(cSeq, " ");
    steps := steps + SumDigits(bSeq) + |bSeq| + SumDigits(cSeq) + |cSeq|
      + |JoinInts(bSeq, " ")| + |JoinInts(cSeq, " ")| + 3;
  }
}
