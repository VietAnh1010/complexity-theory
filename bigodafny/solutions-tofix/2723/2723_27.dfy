// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n+m)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-20
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The nested while loops building bArr and cArr run a combined total
//     of sum(a_list) iterations regardless of n, since the inner while j
//     bound is data-dependent per i and the outputs bSeq/cSeq have length
//     lenB/lenC = 1+sum(a_list); the Python mirrors this with 'for j in
//     range(a[i])' inside 'for i in range(1,n+1)', giving O(n+S) for both,
//     not O(n*S).
//
//   how this label could be wrong, and what to check:
//     The label claims a product n*m, but the b/c-building loops are an
//     outer pass over n=|a_list| with an inner data-dependent loop whose
//     total iterations across all i equal S = sum(a_list), bounded by the
//     description's 'sum of all ai does not exceed 2*10^5'; check that the
//     inner loop count is a running total capped by S regardless of how it
//     distributes across i, which makes the pair O(n+m) rather than
//     O(n*m).
//
//   structural facts (deterministic, from labelaudit.py):
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

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires |a_list| == n + 1
  requires n >= 0
{
  var lenB := 1;
  var i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    lenB := lenB + a_list[i];
    i := i + 1;
  }
  var lenC := 1;
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    lenC := lenC + a_list[i];
    i := i + 1;
  }
  if lenB < 1 { lenB := 1; }
  if lenC < 1 { lenC := 1; }

  var bArr := new int[lenB];
  bArr[0] := 0;
  var pos := 1;
  var cur := 1;
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    var j := 0;
    while j < a_list[i]
      invariant 0 <= j
    {
      if pos < lenB {
        bArr[pos] := cur;
      }
      pos := pos + 1;
      j := j + 1;
    }
    cur := cur + a_list[i];
    i := i + 1;
  }

  var cArr := new int[lenC];
  cArr[0] := 0;
  pos := 1;
  cur := 1;
  i := 1;
  while i <= n
    invariant 1 <= i <= n + 1
  {
    if a_list[i] > 1 && a_list[i - 1] > 1 {
      if pos < lenC { cArr[pos] := cur - 1; }
      pos := pos + 1;
      var j := 1;
      while j < a_list[i]
        invariant 1 <= j
      {
        if pos < lenC { cArr[pos] := cur; }
        pos := pos + 1;
        j := j + 1;
      }
    } else {
      var j := 0;
      while j < a_list[i]
        invariant 0 <= j
      {
        if pos < lenC { cArr[pos] := cur; }
        pos := pos + 1;
        j := j + 1;
      }
    }
    cur := cur + a_list[i];
    i := i + 1;
  }

  var bSeq := bArr[..];
  var cSeq := cArr[..];
  if bSeq == cSeq {
    output := "perfect\n";
  } else {
    output := "ambiguous\n" + JoinInts(bSeq, " ") + "\n" + JoinInts(cSeq, " ") + "\n";
  }
}
