// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-d01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The main loop runs |bx| = n + (binary length of x) times and each
//     FCost90 call is linear in |bs| (ParseBinary90, Pow2_90(n-1),
//     LowSum90), so the cost is O((n + log L)**2), a value term in L that
//     the label omits; the n <= 30 and L <= 1e9 caps do not make it
//     constant. The Python pays the same via bin(x) and per-candidate
//     int(bs, 2) work.
//
//   how this label could be wrong, and what to check:
//     The label counts only n (bottle types). Check the length of bx: it
//     is n zeros plus IntToBinary90(x), the binary digits of the value L,
//     so the loop over |bx| and the per-iteration FCost90 depend on log L
//     as well as n.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 80, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 5, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 913_C. Party Lemonade  (problem 514, solution 514_90)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def f(bs):
//     return int(bs, 2) // (1 << n - 1) * a[-1] + sum(a[i] for i in range(min(n - 1, len(bs))) if bs[-i - 1] == '1')
// n, x = map(int, input().split())
// *a, = map(int, input().split())
// for i in range(1, n):
//     a[i] = min(a[i], 2 * a[i - 1])
// bx = '0' * n + bin(x)[2:]
// ans = f(bx)
// for i in range(len(bx)):
//     if bx[i] == '0':
//         ans = min(ans, f(bx[:i] + '1' + '0' * (len(bx) - i - 1)))
// print(ans)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"

lemma RepeatLen514(s: string, k: nat)
  requires |s| == 1
  ensures |Repeat(s, k)| == k
  decreases k
{
  if k > 0 { RepeatLen514(s, k - 1); }
}

lemma BinPosSteps514(x: int)
  requires x >= 1
  ensures IntToBinaryPos90_steps(x) + 6 == 8 * |IntToBinaryPos90(x)|
  decreases x
{
  if x > 1 { BinPosSteps514(x / 2); }
}

lemma BinSteps514(x: int)
  requires x >= 0
  ensures IntToBinary90_steps(x) <= 8 * |IntToBinary90(x)| + 2
  ensures |IntToBinary90(x)| >= 1
{
  if x > 0 { BinPosSteps514(x); assert |IntToBinaryPos90(x)| >= 1 by { BinPosPositive514(x); } }
}

lemma BinPosPositive514(x: int)
  requires x >= 1
  ensures |IntToBinaryPos90(x)| >= 1
  decreases x
{
  if x > 1 { BinPosPositive514(x / 2); }
}

lemma ParseSteps514(bs: string)
  ensures ParseBinary90_steps(bs) == 13 * |bs| + 3
  decreases |bs|
{
  if |bs| > 0 { ParseSteps514(bs[..|bs| - 1]); }
}

lemma PowSteps514(e: int)
  requires e >= 0
  ensures Pow2_90_steps(e) == 4 * e + 2
  decreases e
{
  if e > 0 { PowSteps514(e - 1); }
}

lemma LowSteps514(bs: string, a: seq<int>, i: int, limit: int)
  requires 0 <= i <= limit && limit <= |bs| && limit <= |a|
  ensures LowSum90_steps(bs, a, i, limit) <= 19 * (limit - i) + 5
  decreases limit - i
{
  if i < limit { LowSteps514(bs, a, i + 1, limit); }
}

lemma FSteps514(bs: string, n: int, a: seq<int>)
  requires n >= 1
  requires |a| == n
  requires n - 1 <= |bs|
  ensures FCost90_steps(bs, n, a) <= 36 * |bs| + 21
{
  var L := |bs|;
  var lim := if n - 1 <= L then n - 1 else L;
  ParseSteps514(bs);
  PowSteps514(n - 1);
  LowSteps514(bs, a, 0, lim);
}

method Solve(n: int, total_score: int, scores: seq<int>)
    returns (output: string, ghost steps: nat)
  requires n >= 1
  requires |scores| == n
  requires total_score >= 0
  ensures steps <= (n + |IntToBinary90(total_score)|) * (38 * (n + |IntToBinary90(total_score)|) + 34) + 48 * (n + |IntToBinary90(total_score)|) + 20 + |output|
{
  steps := 0;
  var x := total_score;
  var a := scores;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |a| == n
    invariant steps <= 11 * (i - 1)
    decreases n - i
  {
    steps := steps + 2;
    steps := steps + 3;
    var cand := 2 * a[i - 1];
    steps := steps + (4 + if a[i] < cand then 1 else 0);
    a := a[i := if a[i] < cand then a[i] else cand];
    steps := steps + 1;
    i := i + 1;
  }
  steps := steps + 1;
  BinSteps514(x);
  RepeatLen514("0", n);
  steps := steps + (|"0"| * n + IntToBinary90_steps(x) + |IntToBinary90(x)|);
  var bx := Repeat("0", n) + IntToBinary90(x);
  ghost var b: nat := |IntToBinary90(x)|;
  ghost var L: nat := n + b;
  assert |bx| == L;
  steps := steps + FCost90_steps(bx, n, a);
  FSteps514(bx, n, a);
  var ans := FCost90(bx, n, a);
  ghost var K: nat := 38 * L + 34;
  ghost var s0 := steps;
  var j := 0;
  while j < |bx|
    invariant 0 <= j <= |bx|
    invariant steps <= s0 + j * K
    decreases |bx| - j
  {
    CostMulDistrib(j, 1, j + 1, K);
    steps := steps + 3;
    steps := steps + 2;
    if bx[j] == '0' {
      RepeatLen514("0", |bx| - j - 1);
      steps := steps + (4 + |"1"| + |"0"| * (|bx| - j - 1) + |Repeat("0", |bx| - j - 1)|);
      var candStr := bx[..j] + "1" + Repeat("0", |bx| - j - 1);
      assert |candStr| == L;
      steps := steps + FCost90_steps(candStr, n, a);
      FSteps514(candStr, n, a);
      var candVal := FCost90(candStr, n, a);
      steps := steps + 2;
      ans := if candVal < ans then candVal else ans;
    }
    steps := steps + 1;
    j := j + 1;
  }
  steps := steps + 2;
  IntToStringDigits(ans);
  steps := steps + (Digits(ans) + |"\n"|);
  output := IntToString(ans) + "\n";
}

function Pow2_90(e: int): int
  requires e >= 0
  ensures Pow2_90(e) >= 1
  decreases e
{
  if e == 0 then
    1
  else
    2 * Pow2_90(e - 1)
}

ghost function Pow2_90_steps(e: int): nat
  requires e >= 0
  decreases e
{
  2 + if e == 0 then 0 else 2 + Pow2_90_steps(e - 1)
}

function ParseBinary90(bs: string): int
  decreases |bs|
{
  if |bs| == 0 then
    0
  else
    ParseBinary90(bs[..|bs| - 1]) * 2 + if bs[|bs| - 1] == '1' then 1 else 0
}

ghost function ParseBinary90_steps(bs: string): nat
  decreases |bs|
{
  3 + if |bs| == 0 then 0 else 10 + ParseBinary90_steps(bs[..|bs| - 1])
}

function IntToBinaryPos90(x: int): string
  requires x >= 1
  decreases x
{
  if x == 1 then
    "1"
  else
    IntToBinaryPos90(x / 2) + [if x % 2 == 1 then '1' else '0']
}

ghost function IntToBinaryPos90_steps(x: int): nat
  requires x >= 1
  decreases x
{
  2 + if x == 1 then 0 else 5 + IntToBinaryPos90_steps(x / 2) + |[if x % 2 == 1 then '1' else '0']|
}

function IntToBinary90(x: int): string
  requires x >= 0
{
  if x == 0 then
    "0"
  else
    IntToBinaryPos90(x)
}

ghost function IntToBinary90_steps(x: int): nat
  requires x >= 0
{
  2 + if x == 0 then 0 else IntToBinaryPos90_steps(x)
}

function LowSum90(bs: string, a: seq<int>, i: int, limit: int): int
  decreases limit - i
{
  if i >= limit || i < 0 || limit > |bs| || limit > |a| then
    0
  else
    (if bs[|bs| - 1 - i] == '1' then a[i] else 0) + LowSum90(bs, a, i + 1, limit)
}

ghost function LowSum90_steps(bs: string, a: seq<int>, i: int, limit: int): nat
  decreases limit - i
{
  5 + (if i >= limit then 0 else 1) + (if i >= limit || i < 0 then 0 else 2) + (if i >= limit || i < 0 || limit > |bs| then 0 else 2) + if i >= limit || i < 0 || limit > |bs| || limit > |a| then 0 else 8 + (if bs[|bs| - 1 - i] == '1' then 1 else 0) + LowSum90_steps(bs, a, i + 1, limit)
}

function FCost90(bs: string, n: int, a: seq<int>): int
  requires n >= 1
  requires |a| == n
{
  var L := |bs|;
  var lim := if n - 1 <= L then n - 1 else L;
  ParseBinary90(bs) / Pow2_90(n - 1) * a[n - 1] + LowSum90(bs, a, 0, lim)
}

ghost function FCost90_steps(bs: string, n: int, a: seq<int>): nat
  requires n >= 1
  requires |a| == n
{
  10 + var L := |bs|; (if n - 1 <= L then 1 else 0) + var lim := if n - 1 <= L then n - 1 else L; ParseBinary90_steps(bs) + Pow2_90_steps(n - 1) + LowSum90_steps(bs, a, 0, lim)
}

import opened Prelude
