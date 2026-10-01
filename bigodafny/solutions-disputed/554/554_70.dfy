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
//     Solve loops over the tests once; inside, `while i < 100 - K` runs a
//     literal 100 times with a j loop to K, and RepeatChar('9', x / 9)
//     plus ParseDecimal cost O(N/9) per candidate, so the cost is linear
//     in the number of tests times per-test value terms in N and K, not
//     quadratic in anything. The Python pays the same ('9' * int(x // 9)
//     and the range(j) loops), so the label is wrong.
//
//   how this label could be wrong, and what to check:
//     The label seems to read the nested loops as quadratic in the number
//     of tests. Check which loops are bounded by the test count: only
//     `while idx < |pairs|` is, and everything inside is bounded by the
//     per-test values N and K (and the literal 100).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 73, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join"],
//     "loop_depth": 3, "loops": 3, "recursive_helpers": 3,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1373_E. Sum of Digits  (problem 554, solution 554_70)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import sys
// sys.setrecursionlimit(10**7)
// 
// for _ in range(int(input())):
// 	N, K = map(int, input().split());ans = float("inf")
// 	for i in range(100 - K):
// 		val = 0
// 		for j in range(i, i + K + 1):val += sum(list(map(int, list(str(j)))))
// 		if (N - val) % (K + 1) == 0 and N >= val:x = int((N - val) // (K + 1));tail = str(x % 9) + str("9") * int(x // 9);ans = min(ans, (int(tail + "0" + str(i)) if i < 10 else int(tail + str(i))))
// 
// 	print(-1) if ans == float("inf") else print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, pairs: seq<(int, int)>) returns (output: string)
  requires forall t :: 0 <= t < |pairs| ==> 1 <= pairs[t].0 <= 150 && 0 <= pairs[t].1 <= 9
{

  var results: seq<string> := [];
  var idx := 0;
  while idx < |pairs|
    invariant 0 <= idx <= |pairs|
    invariant forall t :: 0 <= t < |pairs| ==> 1 <= pairs[t].0 <= 150 && 0 <= pairs[t].1 <= 9
    decreases |pairs| - idx
  {
    var N := pairs[idx].0;
    var K := pairs[idx].1;
    var haveAns := false;
    var ans := 0;
    var i := 0;
    while i < 100 - K
      invariant 0 <= i
      decreases 100 - K - i
    {
      var val := 0;
      var j := i;
      while j <= i + K
        invariant i <= j
        decreases i + K - j
      {
        val := val + DigitSum(j);
        j := j + 1;
      }
      if (N - val) % (K + 1) == 0 && N >= val {
        var x := (N - val) / (K + 1);
        var tail := IntToString(x % 9) + RepeatChar('9', x / 9);
        var cand := ParseDecimal(tail + PadTwo(i));
        if !haveAns || cand < ans {
          ans := cand;
          haveAns := true;
        }
      }
      i := i + 1;
    }
    results := results + [if haveAns then IntToString(ans) else "-1"];
    idx := idx + 1;
  }
  output := Join(results, "\n");
}


function DigitSum(x: int): int
  requires x >= 0
  decreases x
{
  if x < 10 then x else x % 10 + DigitSum(x / 10)
}

function RepeatChar(c: char, k: int): string
  requires k >= 0
  decreases k
{
  if k == 0 then "" else [c] + RepeatChar(c, k - 1)
}

function PadTwo(i: int): string
{
  if i < 10 then "0" + IntToString(i) else IntToString(i)
}

function ParseDecimalFrom(s: string, i: int, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i >= |s| then acc
  else ParseDecimalFrom(s, i + 1, acc * 10 + ((s[i] as int) - ('0' as int)))
}

function ParseDecimal(s: string): int
{
  ParseDecimalFrom(s, 0, 0)
}
