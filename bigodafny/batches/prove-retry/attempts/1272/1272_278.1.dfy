// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-u01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve sorts n strings by |x| < |y| in O(n log n) and then makes n-1
//     substring checks each scanning the haystack string, O(m) per check,
//     so O(n log n + n*m); the Python's arr.sort(key=len) and find per
//     adjacent pair pay the same, so the label omits the width.
//
//   how this label could be wrong, and what to check:
//     The label O(nlogn) counts only the Sort of the n strings by length.
//     Find Contains1272b(arr[i+1], arr[i]) in the loop over arr:
//     ContainsFrom1272b walks every position of the haystack, so each of
//     n-1 pairs costs a width m. If you consider m negligible the label
//     stands; otherwise the class is O(n log n + n*m).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 40, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     2, "recursive_helpers": 2, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": ["Sort"], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 988_B. Substrings Sort  (problem 1272, solution 1272_278)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solve(arr):
//     for i in range(0,len(arr)-1):
//         x = arr[i+1].find(arr[i])
//        # print(x)
//         if x == -1:
//             return 0
//     return 1
// n=int(input())
// arr = []
// while n:
//     s = str(input())
//     arr.append(s)
//     n=n-1
// arr.sort(key=len)
// flag = solve(arr)
// if flag:
//     print("YES")
//     for i in arr:
//         print(i)
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsFrom1272b(hay: string, needle: string, pos: nat): bool
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  if pos + |needle| > |hay| then false
  else if hay[pos..pos+|needle|] == needle then true
  else ContainsFrom1272b(hay, needle, pos + 1)
}

function Contains1272b(hay: string, needle: string): bool
{
  |needle| == 0 || ContainsFrom1272b(hay, needle, 0)
}

ghost function MaxLen1272(s: seq<string>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else if |s[0]| >= MaxLen1272(s[1..]) then |s[0]| else MaxLen1272(s[1..])
}

lemma MaxLenOk1272(s: seq<string>, x: string)
  requires x in s
  ensures |x| <= MaxLen1272(s)
  decreases |s|
{
  if s[0] != x { assert x in s[1..]; MaxLenOk1272(s[1..], x); }
}

ghost function CC1272(h: string, nl: string, pos: nat): nat
  requires 1 <= |nl| && pos <= |h|
  decreases |h| - pos
{
  if pos + |nl| > |h| then 1
  else |nl| + 3 + (if h[pos..pos+|nl|] == nl then 0 else CC1272(h, nl, pos + 1))
}

lemma CCBound1272(h: string, nl: string, pos: nat)
  requires 1 <= |nl| && pos <= |h|
  ensures CC1272(h, nl, pos) <= (|h| - pos + 1) * (|nl| + 3)
  decreases |h| - pos
{
  CostMulDistrib(1, |h| - pos, |h| - pos + 1, |nl| + 3);
  if pos + |nl| > |h| {
  } else if h[pos..pos+|nl|] == nl {
  } else {
    CCBound1272(h, nl, pos + 1);
    CostMulDistrib(1, |h| - pos - 1, |h| - pos, |nl| + 3);
    CostMulDistrib(1, |h| - pos, |h| - pos + 1, |nl| + 3);
  }
}

lemma PBound1272(h: string, nl: string, M: nat)
  requires 1 <= |nl| <= M && |h| <= M
  ensures CC1272(h, nl, 0) <= (M + 1) * (M + 3)
{
  CCBound1272(h, nl, 0);
  CostMulMonoLeft(|h| + 1, M + 1, |nl| + 3);
  CostMulMono(M + 1, |nl| + 3, M + 3);
}

method Solve(n: int, strings: seq<string>) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * NLogN(|strings|) + |strings| * ((MaxLen1272(strings) + 1) * (MaxLen1272(strings) + 3) + 8) + 12 * |strings| + 20 + 2 * |output|
{
  steps := 1;
  var N := |strings|;
  var arr := Sort(strings, (x: string, y: string) => |x| < |y|);
  SortKeepsElems(strings, (x: string, y: string) => |x| < |y|);
  steps := steps + SortCost(N);
  SortCostWithin(N, N);
  ghost var M := MaxLen1272(strings);
  ghost var P: nat := (M + 1) * (M + 3);
  ghost var K: nat := P + 8;
  ghost var B := steps;
  var flag := true;
  var i := 0;
  steps := steps + 3;
  while i < |arr| - 1
    invariant 0 <= i <= |arr|
    invariant |arr| == N
    invariant steps <= B + 3 + i * K
    decreases |arr| - 1 - i
  {
    assert arr[i] in arr && arr[i+1] in arr;
    MaxLenOk1272(strings, arr[i]);
    MaxLenOk1272(strings, arr[i+1]);
    if |arr[i]| >= 1 { PBound1272(arr[i+1], arr[i], M); }
    if !Contains1272b(arr[i+1], arr[i]) { flag := false; }
    CostMulDistrib(i, 1, i + 1, K);
    i := i + 1;
    steps := steps + K;
  }
  CostMulMonoLeft(i, N, K);
  if flag {
    var lines: seq<string> := ["YES"];
    var m := 0;
    steps := steps + 2;
    while m < |arr|
      invariant 0 <= m <= |arr|
      invariant |lines| == m + 1
      invariant steps <= B + 5 + N * K + 5 * m
      decreases |arr| - m
    {
      lines := lines + [arr[m]];
      m := m + 1;
      steps := steps + 5;
    }
    JoinLen(lines, "\n");
    output := Join(lines, "\n");
    steps := steps + SumLen(lines) + |lines|;
  } else {
    output := "NO";
    steps := steps + 1;
  }
}
