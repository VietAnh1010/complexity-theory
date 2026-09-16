// 172_A. Phone Code  (problem 1484, solution 1484_26)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=[];i=0
// for _ in range(int(input())):l.append(input())
// a=max(l);b=min(l)
// while a[i]==b[i]:i+=1
// print(i)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

// StringLess(a, b) recurses on |a| (its `decreases`), so each call is charged
// |a|. Unlike the sort-based solution to this same problem, this one runs a
// StringLess comparison against `best`/`worst` on EVERY loop iteration, not
// once total after sorting -- so the per-iteration cost is bounded by the
// length of the tracked extremes, not amortized across the whole input. That
// gives a genuinely multiplicative bound in n and the max string length, not
// the additive O(n + SumLen) the sorted variant gets. See `why disagrees`
// below: this is a finding, not a workaround.
ghost function MaxLen(xs: seq<string>): nat
{
  if |xs| == 0 then 0
  else if |xs[0]| >= MaxLen(xs[1..]) then |xs[0]| else MaxLen(xs[1..])
}

lemma MaxLenBound(xs: seq<string>, x: string)
  requires x in xs
  ensures |x| <= MaxLen(xs)
  decreases |xs|
{
  if xs[0] == x {
  } else {
    MaxLenBound(xs[1..], x);
  }
}

// Isolated so Z3 never has to discover the distributive step itself.
lemma DistribStep(idx: int, m: int)
  requires idx >= 1
  ensures 6 * (idx - 1) * m + 6 * m == 6 * idx * m
{}

// Disagreement: proved bound is O(n * MaxLen(numbers)), not O(n). The label's
// "n" is the string count; the per-iteration StringLess cost against the
// running best/worst depends on their length, which does not shrink with n.
method Solve(n: int, numbers: seq<string>) returns (output: string, ghost steps: nat)
  requires |numbers| == n
  requires n >= 1
  ensures steps <= 6 * |numbers| * MaxLen(numbers) + 4 * MaxLen(numbers) + 6
{
  steps := 1;
  var best := numbers[0];
  var worst := numbers[0];
  assert best in numbers;
  var idx := 1;
  while idx < |numbers|
    invariant 1 <= idx <= |numbers|
    invariant best in numbers
    invariant worst in numbers
    invariant steps <= 6 * (idx - 1) * MaxLen(numbers) + 1
    decreases |numbers| - idx
  {
    assert numbers[idx] in numbers;
    MaxLenBound(numbers, best);
    MaxLenBound(numbers, numbers[idx]);
    if StringLess(best, numbers[idx]) { best := numbers[idx]; }
    MaxLenBound(numbers, numbers[idx]);
    MaxLenBound(numbers, worst);
    if StringLess(numbers[idx], worst) { worst := numbers[idx]; }
    DistribStep(idx, MaxLen(numbers));
    idx := idx + 1;
    steps := steps + 6 * MaxLen(numbers);
  }
  MaxLenBound(numbers, best);
  MaxLenBound(numbers, worst);
  var i := 0;
  while i < |best| && i < |worst| && best[i] == worst[i]
    invariant 0 <= i <= MaxLen(numbers)
    invariant steps <= 6 * (|numbers| - 1) * MaxLen(numbers) + 1 + 4 * i
    decreases |best| - i
  {
    i := i + 1;
    steps := steps + 4;
  }
  output := IntToString(i);
  steps := steps + 1;
  DistribStep(|numbers|, MaxLen(numbers));
}
