// 1203_F1. Complete the Projects (easy version)  (problem 2128, solution 2128_34)
// time complexity: O(n**2)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,r=map(int,input().split())
// a=[list(map(int,input().split())) for i in range(n)]
// pos = []
// neg = []
// ans=0
// for x in a:
// 	if x[1]>0:
// 		pos.append(x)
// 	else:
// 		neg.append(x)
// pos.sort(key=lambda k: k[0])
// flag=True
// for x in pos:
// 	if r>=x[0]:
// 		r+=x[1]
// 		ans+=1
//
// neg.sort(key=lambda i: i[0]+i[1],reverse=True)
// arr=[0]*(r+1)
// for i in range(len(neg)):
// 	for j in range(neg[i][0],r+1):
// 		if j+neg[i][1]>=0:
// 			arr[j+neg[i][1]]=max(arr[j+neg[i][1]],arr[j]+1)
// ans+=max(arr)
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// The second of two `array<T>` rows left in `solutions/`; see `2826_42.dfy` for
// the first and `batches/cost-axioms/PLAN.md` § 2 for the rule they except.
//
// `arr` is sized `r + 1`, and `r` reaches 30000 in this row's own tests. The
// inner loop walks `j` from `neg[i].0` to `r` writing `arr[j + neg[i].1]`, so a
// `seq` rewrite costs O(r) per write and O(r^2 * |neg|) per test -- around 10^9
// element copies at r = 30000, against 88 tests. Rewritten to `seq` the row had
// not finished a single differential test after four minutes; as an array all
// 88 agree in seconds.
//
// As with `2826_42`, this says nothing about the cost model: under the axioms
// the `seq` and `array` versions are charged the same. It says the axioms are
// false of this backend, and here that falsehood decides whether the row runs.

// ---- proof-only scaffolding for Sort's cost (batches/prove-sample/PROMPT.md,
// same SortCost/SquareSplit/QuadTail/SortCostBound block as 1421_89.dfy) ----
ghost function {:opaque} SortCost(k: nat): nat
  decreases k
{
  if k <= 1 then 1
  else SortCost(k / 2) + SortCost(k - k / 2) + k
}

lemma SquareSplit(k: nat, L: nat)
  requires 2 * L <= k <= 2 * L + 1
  ensures 2 * L * L + 2 * (k - L) * (k - L) <= k * k + 1
{
  var d := k - 2 * L;
  assert d == 0 || d == 1;
  assert k - L == L + d;
  assert 2 * L * L + 2 * (k - L) * (k - L) == 4 * L * L + 4 * L * d + 2 * d * d;
  assert k == 2 * L + d;
  assert k * k == 4 * L * L + 4 * L * d + d * d;
  assert d * d <= 1;
}

lemma QuadTail(k: nat)
  requires k >= 2
  ensures k * k + k + 3 <= 2 * k * k + 1
{
  assert (k - 2) * (k + 1) >= 0;
}

lemma SortCostBound(k: nat)
  ensures SortCost(k) <= 2 * k * k + 1
  decreases k
{
  reveal SortCost();
  if k <= 1 {
  } else {
    var L := k / 2;
    var R := k - L;
    SortCostBound(L);
    SortCostBound(R);
    SquareSplit(k, L);
    assert SortCost(k) == SortCost(L) + SortCost(R) + k;
    assert SortCost(L) + SortCost(R) + k <= (2 * L * L + 1) + (2 * R * R + 1) + k;
    assert (2 * L * L + 1) + (2 * R * R + 1) + k == 2 * L * L + 2 * R * R + k + 2;
    assert 2 * L * L + 2 * R * R + k + 2 <= (k * k + 1) + k + 2;
    QuadTail(k);
  }
}

lemma MergeLength<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures |Merge(a, b, less)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeLength(a, b[1..], less);
  } else {
    MergeLength(a[1..], b, less);
  }
}

lemma SortLen<T>(s: seq<T>, less: (T, T) -> bool)
  ensures |Sort(s, less)| == |s|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortLen(s[..|s| / 2], less);
    SortLen(s[|s| / 2..], less);
    MergeLength(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

lemma MulMonoRight(x: nat, p: nat, q: nat)
  requires p <= q
  ensures x * p <= x * q
{ }

lemma SquareMono(k: nat, N: nat)
  requires k <= N
  ensures k * k <= N * N
{
  MulMonoRight(k, k, N);
  MulMonoRight(N, k, N);
}

// Isolated so the final numeric combination is a small, self-contained
// query: no opaque SortCost calls, no array/loop state in scope, just plain
// nat arithmetic. Folding this into an inline `assert` at the end of Solve
// timed out (too much ambient loop-invariant context for Z3 to sift).
lemma FinalBound(N: nat, P: nat, Q: nat, sp: nat, sn: nat, r: nat, spanTotal: nat)
  requires P <= N
  requires Q <= N
  requires sp <= 2 * N * N + 1
  requires sn <= 2 * N * N + 1
  ensures sp + sn + 5 * N + 3 * P + 3 * Q + 2 * r + 6 * spanTotal + 5
       <= 4 * N * N + 20 * N + 3 * r + 6 * spanTotal + 20
{ }

// Label O(n**2). Convention (batches/prove-sample/PROMPT_convention.md § "What
// changed"): a bound may name an input value, so `r` is a legitimate parameter
// -- exposed here as ghost out-param `r_final` since `r` is a local whose final
// value depends on which `pos` elements get admitted, not a formal parameter.
//
// The two `Sort` calls are each charged the honest O(k^2) `SortCost` bound
// (not merge sort's true n log n), with `|pos|, |neg| <= |data_list|` via
// `SquareMono`.
//
// The `arr`-fill double loop is NOT bounded as `|neg| * (r+1)`: the row's
// preconditions put no lower bound on `neg[i].0` (a raw input value), so the
// inner `while j <= r` can run far more than `r+1` times if some position is
// very negative -- range(-10**9, r+1) costs ~10**9 either way, in the
// original Python too. Adding a `requires neg[i].0 >= 0` would dodge exactly
// the problem PROMPT_convention.md forbids dodging, so instead the true
// per-`neg`-element span is charged exactly (ghost accumulator `spanTotal`,
// exposed as `span_total`) rather than assumed bounded by `r`.
method {:vcs_split_on_every_assert} Solve(n: int, m: int, data_list: seq<seq<int>>) returns (output: string, ghost steps: nat, ghost r_final: nat, ghost span_total: nat)
  requires m >= 0
  requires forall k :: 0 <= k < |data_list| ==> |data_list[k]| >= 2
  ensures steps <= 4 * |data_list| * |data_list| + 20 * |data_list| + 3 * r_final + 6 * span_total + 20
{
  var pos: seq<(int,int)> := [];
  var neg: seq<(int,int)> := [];
  var idx := 0;
  steps := 1;
  while idx < |data_list|
    invariant 0 <= idx <= |data_list|
    invariant |pos| <= idx
    invariant |neg| <= idx
    invariant steps <= 1 + 5 * idx
    decreases |data_list| - idx
  {
    var xi := data_list[idx];
    if xi[1] > 0 {
      pos := pos + [(xi[0], xi[1])];
    } else {
      neg := neg + [(xi[0], xi[1])];
    }
    idx := idx + 1;
    steps := steps + 5;
  }
  SortCostBound(|pos|);
  SquareMono(|pos|, |data_list|);
  SortLen(pos, (p: (int,int), q: (int,int)) => p.0 < q.0);
  assert SortCost(|pos|) <= 2 * |data_list| * |data_list| + 1;
  steps := steps + SortCost(|pos|);
  pos := Sort(pos, (p: (int,int), q: (int,int)) => p.0 < q.0);
  var r := m;
  var ans := 0;
  var pi := 0;
  while pi < |pos|
    invariant 0 <= pi <= |pos|
    invariant r >= 0
    invariant steps <= 1 + 5 * |data_list| + SortCost(|pos|) + 3 * pi
    decreases |pos| - pi
  {
    if r >= pos[pi].0 {
      r := if r + pos[pi].1 >= 0 then r + pos[pi].1 else 0;
      ans := ans + 1;
    }
    pi := pi + 1;
    steps := steps + 3;
  }
  r_final := r;
  SortCostBound(|neg|);
  SquareMono(|neg|, |data_list|);
  SortLen(neg, (p: (int,int), q: (int,int)) => p.0 + p.1 > q.0 + q.1);
  assert SortCost(|neg|) <= 2 * |data_list| * |data_list| + 1;
  steps := steps + SortCost(|neg|);
  neg := Sort(neg, (p: (int,int), q: (int,int)) => p.0 + p.1 > q.0 + q.1);
  var arr := new int[r + 1](kk => 0);
  steps := steps + (r + 1);

  var ni := 0;
  ghost var spanTotal: nat := 0;
  while ni < |neg|
    invariant 0 <= ni <= |neg|
    invariant steps <= 1 + 5 * |data_list| + SortCost(|pos|) + 3 * |pos|
                      + SortCost(|neg|) + (r + 1) + 6 * spanTotal + 3 * ni
    decreases |neg| - ni
  {
    steps := steps + 3;
    var j := neg[ni].0;
    ghost var start := j;
    ghost var startSteps := steps;
    while j <= r
      invariant j >= start
      invariant steps == startSteps + 6 * (j - start)
      decreases r - j + 1
    {
      if 0 <= j <= r && j + neg[ni].1 >= 0 {
        var target := j + neg[ni].1;
        if target <= r {
          var cand := arr[j] + 1;
          if cand > arr[target] {
            arr[target] := cand;
          }
        }
      }
      j := j + 1;
      steps := steps + 6;
    }
    ghost var innerCount: nat := j - start;
    spanTotal := spanTotal + innerCount;
    ni := ni + 1;
  }
  span_total := spanTotal;

  var best := arr[0];
  var bi := 1;
  while bi < arr.Length
    invariant 1 <= bi <= arr.Length
    invariant steps <= 1 + 5 * |data_list| + SortCost(|pos|) + 3 * |pos|
                      + SortCost(|neg|) + (r + 1) + 6 * spanTotal + 3 * |neg| + bi
    decreases arr.Length - bi
  {
    if arr[bi] > best { best := arr[bi]; }
    bi := bi + 1;
    steps := steps + 1;
  }
  ans := ans + best;
  output := IntToString(ans) + "\n";
  steps := steps + 2;
  FinalBound(|data_list|, |pos|, |neg|, SortCost(|pos|), SortCost(|neg|), r, spanTotal);
  assert steps <= 4 * |data_list| * |data_list| + 20 * |data_list| + 3 * r_final + 6 * span_total + 20;
}
