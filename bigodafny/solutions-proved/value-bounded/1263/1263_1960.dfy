// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-03
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Each test pays `while v != 0` with v := v / 10, which runs
//     log10(a_i) times, plus Sort on at most that many round numbers,
//     giving O(n log max a_i) in the test count and values; the Python has
//     the same digit loop and sort, so the label's n is not the growth
//     variable.
//
//   how this label could be wrong, and what to check:
//     The label assumes cost depends on the count n with a log factor from
//     sorting. The digit loop `while v != 0` runs once per decimal digit
//     of each value, so check whether the cost is log(a_i) per test rather
//     than log(n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 34, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "JoinInts"],
//     "loop_depth": 2, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     ["Sort"], "uses_map": false, "uses_multiset": false, "uses_set":
//     false}
// --------------------------------------------------------------------

// 1352_A. Sum of Round Numbers  (problem 1263, solution 1263_1960)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// import sys
// 
// ip = lambda : sys.stdin.readline()
// ipl = lambda : sys.stdin.readline().split()
// 
// for _ in range(int(ip())):
// 	n = int(input())
// 	res = []
// 	k = 1
// 	while n:
// 		if n % 10 != 0:
// 			res.append(n%10 * k)
// 		n //= 10
// 		k *= 10
// 	print(len(res))
// 	res.sort(reverse=True)
// 	print(*res)
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n == |a_list|
  requires forall k :: 0 <= k < n ==> a_list[k] >= 1
  ensures steps <= 1 + n * (12 + 9 * MaxDig1263(a_list) + 2 * NLogN(MaxDig1263(a_list))) + 2 * n + 2 * |output|
{
{
  steps := 1;
  ghost var D := MaxDig1263(a_list);
  ghost var K0 := 12 + 9 * D + 2 * NLogN(D);

  var results: seq<string> := [];
  var t := 0;
  while t < n
    invariant 0 <= t <= n
    invariant |results| == 2 * t
    invariant steps <= 1 + t * K0 + SumLen(results)
    decreases n - t
  {
    MaxDigElem1263(a_list, t);
    steps := steps + 6;
    var v := a_list[t];
    ghost var s0 := steps;
    ghost var it: nat := 0;
    var res: seq<int> := [];
    var kk := 1;
    while v != 0
      invariant v >= 0
      invariant it + DigCnt1263(v) == DigCnt1263(a_list[t])
      invariant |res| <= it
      invariant steps == s0 + 8 * it
      decreases v
    {
      var d := v % 10;
      if d != 0 {
        res := res + [d * kk];
      }
      v := v / 10;
      kk := kk * 10;
      it := it + 1;
      steps := steps + 8;
    }
    var sorted := Sort(res, (x: int, y: int) => x > y);
    steps := steps + SortCost(|res|);
    SortCostWithin(|res|, D);
    ghost var r0 := results;
    ghost var js := JoinInts(sorted, " ");
    results := results + [IntToString(|res|), JoinInts(sorted, " ")];
    IntToStringDigits(|res|);
    SumDigitsLe1263(sorted);
    steps := steps + 2 + Digits(|res|) + SumDigits(sorted) + |sorted|;
    SumLenSnoc(r0, IntToString(|res|));
    SumLenSnoc(r0 + [IntToString(|res|)], js);
    assert results == (r0 + [IntToString(|res|)]) + [js];
    CostMulDistrib(t, 1, t + 1, K0);
    t := t + 1;
  }
  output := Join(results, "\n");
  steps := steps + SumLen(results) + |results|;
  if |results| >= 1 { JoinLen(results, "\n"); }
}
}

ghost function DigCnt1263(v: int): nat
  decreases if v < 0 then 0 else v
{
  if v <= 0 then 0 else 1 + DigCnt1263(v / 10)
}

ghost function MaxDig1263(s: seq<int>): nat
  decreases |s|
{
  if |s| == 0 then 0 else if DigCnt1263(s[0]) >= MaxDig1263(s[1..]) then DigCnt1263(s[0]) else MaxDig1263(s[1..])
}

lemma MaxDigElem1263(s: seq<int>, k: nat)
  requires k < |s|
  ensures DigCnt1263(s[k]) <= MaxDig1263(s)
  decreases k
{
  if k > 0 { MaxDigElem1263(s[1..], k - 1); }
}

lemma SumDigitsLe1263(xs: seq<int>)
  ensures SumDigits(xs) <= |JoinInts(xs, " ")|
{
  if |xs| >= 1 { JoinIntsLen(xs, " "); }
  else { assert SumDigits(xs) == 0; }
}
