// VALUE-BOUNDED -- filed for review; the proof carries a term the label omits.
//
//   This proof's bound depends on the MAGNITUDE of an input, not only on how
//   many inputs there are. BigOBench fitted the label by profiling, which
//   treats a capped value as constant; COMPLEXITY.md section 1 decides the
//   opposite, so the two disagree here by construction.
//
//   See solutions-proved/value-bounded/README.md for the category and
//   MANIFEST.jsonl for this row's entry.
//
// 1349_A. Orac and LCM  (problem 1871, solution 1871_291)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def gcd(a, b):
//     while b:
//         a, b = b, a % b
//     return a
//
// def solve(array):
//     lcm = (array[0] * array[1])//gcd(array[0], array[1])
//     current = lcm
//     for i in range(2, len(array)):
//         running = (current * array[i])//gcd(current, array[i])
//         lcm = gcd(lcm, running)
//         current = gcd(current, array[i])
//     print(lcm)
//     return
//
// n = int(input())
// arr = list(map(int, input().split(' ')))
// solve(arr)
// --------------------------------------------------------------------

include "../../../../prelude.dfy"
import opened Prelude

lemma GcdNonneg(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures Gcd(a, b) >= 0
  decreases b
{
  if b == 0 {
  } else {
    GcdNonneg(b, a % b);
  }
}

lemma GcdPositive(a: int, b: int)
  requires a >= 0 && b >= 0
  requires a >= 1 || b >= 1
  ensures Gcd(a, b) >= 1
  decreases b
{
  if b == 0 {
  } else {
    GcdPositive(b, a % b);
  }
}

lemma MulDivBounds(x: int, y: int, g: int)
  requires x >= 0 && y >= 0 && g >= 1
  ensures x * y >= 0 && (x * y) / g >= 0
  ensures x >= 1 && 1 <= g <= y ==> 1 <= (x * y) / g <= x * y
{
  CostMulMono(x, 0, y);
  var p := x * y;
  var q := p / g;
  assert p == g * q + p % g && 0 <= p % g < g;
  if q < 0 {
    CostMulMonoLeft(1, g, -q);
    assert false;
  }
  if x >= 1 && 1 <= g <= y {
    CostMulMonoLeft(1, x, y);
    assert q != 0;
    CostMulMonoLeft(1, g, q);
  }
}

// The three Gcd calls of one iteration, bounded apart from Solve.
lemma IterCost(c: int, x: int, l: int, r: int, l0: int, m: int)
  requires c >= 0 && 1 <= x <= m && 1 <= l <= l0 && r >= 0
  ensures 2 * GcdSteps(c, x) + GcdSteps(l, r) <= 4 * BitLen(m) + 7 + 2 * BitLen(l0)
{
  GcdStepsBound(c, x);
  CeilLog2Monotone(x + 1, m + 1);
  GcdStepsBoundFirst(l, r);
  CeilLog2Monotone(l + 1, l0 + 1);
}

// Each Gcd call costs Euclid's recursion depth, GcdSteps: at most
// 2 * BitLen(max) + 2 on (current, arr[i]) (GcdStepsBound), and at most
// 2 * BitLen(lcm) + 3 on (lcm, running) (GcdStepsBoundFirst). lcm starts at
// arr[0] * arr[1] / gcd and never grows, since a gcd is at most its argument.
method {:isolate_assertions} Solve(n: int, a_list: seq<int>) returns (output: string, ghost steps: nat)
  requires |a_list| >= 2
  requires forall v :: v in a_list ==> v >= 1
  ensures steps <= |a_list| * (10 + 4 * BitLen(MaxSeq(a_list)) + 2 * BitLen(a_list[0] * a_list[1]))
                   + 2 * BitLen(MaxSeq(a_list)) + 7
{
  steps := 1;
  var arr := a_list;
  MaxSeqBound(arr);
  ghost var M := MaxSeq(arr);
  ghost var L := BitLen(M);
  assert arr[0] in arr && arr[1] in arr;
  assert {:split_here} arr[0] >= 1 && arr[1] >= 1;
  GcdPositive(arr[0], arr[1]);
  GcdLeSecond(arr[0], arr[1]);
  CeilLog2Monotone(arr[1] + 1, M + 1);
  GcdStepsBound(arr[0], arr[1]);
  steps := steps + 3 + GcdSteps(arr[0], arr[1]);
  MulDivBounds(arr[0], arr[1], Gcd(arr[0], arr[1]));
  var lcm := (arr[0] * arr[1]) / Gcd(arr[0], arr[1]);
  ghost var lcm0 := lcm;
  ghost var P := BitLen(arr[0] * arr[1]);
  CeilLog2Monotone(lcm0 + 1, arr[0] * arr[1] + 1);
  assert BitLen(lcm0) <= P;
  ghost var K := 10 + 4 * L + 2 * P;
  ghost var base := steps;
  var current := lcm;
  var i := 2;
  while i < |arr|
    invariant 2 <= i <= |arr|
    invariant current >= 0
    invariant 1 <= lcm <= lcm0
    invariant steps <= base + K * (i - 2)
    decreases |arr| - i
  {
    assert {:split_here} arr[i] in arr;
    GcdPositive(current, arr[i]);
    var gi := Gcd(current, arr[i]);
    MulDivBounds(current, arr[i], gi);
    var running := (current * arr[i]) / gi;
    IterCost(current, arr[i], lcm, running, lcm0, M);
    steps := steps + 3 + 2 * GcdSteps(current, arr[i]) + GcdSteps(lcm, running);
    GcdLeFirst(lcm, running);
    lcm := Gcd(lcm, running);
    GcdNonneg(current, arr[i]);
    current := Gcd(current, arr[i]);
    assert K * (i + 1 - 2) == K * (i - 2) + K;
    i := i + 1;
  }
  CostMulMono(K, |arr| - 2, |arr|);
  assert steps <= 6 + 2 * L + K * |arr|;
  assert K * |arr| == |a_list| * (10 + 4 * L + 2 * P);
  output := IntToString(lcm);
  steps := steps + 1;
}
