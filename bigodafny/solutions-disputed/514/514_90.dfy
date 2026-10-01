// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3-fix
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     bx = RepeatChar90('0', n) + IntToBinary90(x) has length n + log2(x),
//     the main loop over j < |bx| calls FCost90 (ParseBinary90 over |bx|)
//     and RepeatChar90 per iteration, so the cost is O((n + log L)**2), a
//     value term in total_score that the label O(n**2) omits. The Python's
//     bin(x), int(bs, 2) and per-i slicing pay the same, so the label is
//     at fault.
//
//   how this label could be wrong, and what to check:
//     The label names only n (the number of bottle types), but the loop
//     over j runs |bx| = n + bitlength(total_score) times and each
//     iteration costs O(|bx|), so the cost depends on the value L. Check
//     IntToBinary90/IntToBinaryPos90 (recursion on x/2) and the Python's
//     bin(x)[2:]; if the intended reading is that L's bit-length is
//     bounded by the 10^9 cap, the statement cap does not make it constant
//     under the value-terms rule, so the mismatch stands.
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

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, total_score: int, scores: seq<int>) returns (output: string)
  requires n >= 1
  requires |scores| == n
  requires total_score >= 0
{
  var x := total_score;
  var a := scores;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |a| == n
    decreases n - i
  {
    var cand := 2 * a[i-1];
    a := a[i := if a[i] < cand then a[i] else cand];
    i := i + 1;
  }
  var bx := RepeatChar90('0', n) + IntToBinary90(x);
  var ans := FCost90(bx, n, a);
  var j := 0;
  while j < |bx|
    invariant 0 <= j <= |bx|
    decreases |bx| - j
  {
    if bx[j] == '0' {
      var candStr := bx[..j] + "1" + RepeatChar90('0', |bx| - j - 1);
      var candVal := FCost90(candStr, n, a);
      ans := if candVal < ans then candVal else ans;
    }
    j := j + 1;
  }
  output := IntToString(ans) + "\n";
}

function Pow2_90(e: int): int
  requires e >= 0
  decreases e
  ensures Pow2_90(e) >= 1
{
  if e == 0 then 1 else 2 * Pow2_90(e - 1)
}

function ParseBinary90(bs: string): int
  decreases |bs|
{
  if |bs| == 0 then 0
  else ParseBinary90(bs[..|bs|-1]) * 2 + (if bs[|bs|-1] == '1' then 1 else 0)
}

function RepeatChar90(c: char, k: int): string
  requires k >= 0
  decreases k
{
  if k == 0 then "" else [c] + RepeatChar90(c, k - 1)
}

function IntToBinaryPos90(x: int): string
  requires x >= 1
  decreases x
{
  if x == 1 then "1"
  else IntToBinaryPos90(x / 2) + [if x % 2 == 1 then '1' else '0']
}

function IntToBinary90(x: int): string
  requires x >= 0
{
  if x == 0 then "0" else IntToBinaryPos90(x)
}

function LowSum90(bs: string, a: seq<int>, i: int, limit: int): int
  decreases limit - i
{
  if i >= limit || i < 0 || limit > |bs| || limit > |a| then 0
  else (if bs[|bs| - 1 - i] == '1' then a[i] else 0) + LowSum90(bs, a, i + 1, limit)
}

function FCost90(bs: string, n: int, a: seq<int>): int
  requires n >= 1
  requires |a| == n
{
  var L := |bs|;
  var lim := if n - 1 <= L then n - 1 else L;
  ParseBinary90(bs) / Pow2_90(n - 1) * a[n-1] + LowSum90(bs, a, 0, lim)
}
