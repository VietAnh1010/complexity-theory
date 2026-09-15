// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(1)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve requires 1 <= n <= 4, so the while loop over n and the
//     MaxSeq/MinSeq calls over xs/ys all run over a problem-capped
//     constant-size input; per the value-bounded-loop rule this is O(1) in
//     both Python and Dafny, so the labelled O(n) is wrong for the label,
//     not the translation.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 40, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "MaxSeq", "MinSeq",
//     "ParseInt", "ParseIntFrom"], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 2, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 596_A. Wilbur and Swimming Pool  (problem 966, solution 966_134)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// x = []
// y = []
// for i in range(n):
//     xi, yi = map(int, input().split())
//     x.append(xi)
//     y.append(yi)
// if n==1:
//     print(-1)
// 
// if n>=2:
//     s = (max(x) - min(x)) * (max(y) - min(y))
//     if s == 0: s = -1
//     print(s)
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ParseIntFrom(s: string, i: nat, acc: int): int
  requires 0 <= i <= |s|
  decreases |s| - i
{
  if i == |s| then acc
  else ParseIntFrom(s, i + 1, acc * 10 + (s[i] as int - '0' as int))
}

function ParseInt(s: string): int
{
  if |s| > 0 && s[0] == '-' then -ParseIntFrom(s, 1, 0)
  else ParseIntFrom(s, 0, 0)
}


method Solve(n: int, values: seq<seq<string>>) returns (output: string)
  requires 1 <= n <= 4
  requires |values| == n
  requires forall k :: 0 <= k < n ==> |values[k]| >= 2
{
  if n == 1 {
    output := "-1";
  } else {
    var xs: seq<int> := [];
    var ys: seq<int> := [];
    var i := 0;
    while i < n
      invariant 0 <= i <= n
      invariant |xs| == i
      invariant |ys| == i
      decreases n - i
    {
      xs := xs + [ParseInt(values[i][0])];
      ys := ys + [ParseInt(values[i][1])];
      i := i + 1;
    }
    var s := (MaxSeq(xs) - MinSeq(xs)) * (MaxSeq(ys) - MinSeq(ys));
    if s == 0 { s := -1; }
    output := IntToString(s);
  }
}
