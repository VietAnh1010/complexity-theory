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
// 750_A. New Year and Hurry  (problem 704, solution 704_351)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import math
//
// n, k = map(int, input().split())
//
// timeToSolve = 240 - k
// problems = math.floor(timeToSolve / 5)
// problems = math.floor((math.sqrt(1 + 8*problems) - 1) / 2)
//
// print(n if problems > n else problems)
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

// The while loop is bounded by `fuel`, a countdown seeded from `prob`, but it
// stops first: it runs while (m+1)*(m+2) <= 2*prob, so it ends with
// m*m <= 2*prob and costs O(sqrt(prob)). `prob` is (240-b)/5, an input VALUE,
// not a size: per the value-vs-size convention it enters the bound as its own
// parameter rather than being folded into a constant. So the honest proof is
// O(sqrt(prob)), not O(1): the label holds only because the Codeforces problem
// caps 0<=k<=240 (never stated in this signature). The Python takes the square
// root in O(1); the Dafny searches for it. relation = looser-structural.
ghost function Prob(b: int): int
{
  FloorDiv(240 - b, 5)
}

ghost function ProbNat(b: int): nat
{
  if Prob(b) > 0 then Prob(b) else 0
}

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= 2 * ISqrt(2 * ProbNat(b)) + 10 + |output|
{
  steps := 1;
  var timeToSolve := 240 - b;
  var prob := FloorDiv(timeToSolve, 5);
  steps := steps + 2;
  var m := 0;
  var fuel := (if prob > 0 then prob else 0) + 2;
  steps := steps + 2;
  while fuel > 0 && (m+1)*(m+2) <= 2*prob
    invariant 0 <= m
    invariant m * m <= 2 * ProbNat(b)
    invariant steps == 2 * m + 5
    decreases fuel
  {
    assert (m+1)*(m+1) <= (m+1)*(m+2);
    m := m + 1;
    fuel := fuel - 1;
    steps := steps + 2;
  }
  LeISqrt(m, 2 * ProbNat(b));
  var ans := if m > a then a else m;
  steps := steps + 1;
  output := IntToString(ans);
  IntToStringDigits(ans);
  steps := steps + Digits(ans);
}
