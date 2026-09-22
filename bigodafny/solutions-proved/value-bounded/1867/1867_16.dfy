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
// 1202_D. Print a 1337-string...  (problem 1867, solution 1867_16)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// import bisect
//
// Q=int(input())
//
// A=[n*(n-1)//2 for n in range(10**5)]
//
//
// x=bisect.bisect(A,10**9)
//
//
// for testcases in range(Q):
//     t=int(input())
//
//     if t==1:
//         print(1337)
//         continue
//
//     x=bisect.bisect_left(A,t)
//
//     ANS="1"+"3"*(x-1-2)+"1"*(t-(A[x-1]))+"337"
//
//     print(ANS)
//
//
//
//
//
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

// The binary search range is capped to [0,100000] regardless of t, so the
// "3"-run is O(1). But the "1"-run length is t - A[x-1], and t is an input
// VALUE with no upper bound stated on `numbers` -- per the value-vs-size
// convention that is a real parameter of the cost, not a constant. This proof
// charges it explicitly as `Pos(numbers[qi])`, giving a bound that also grows
// with the sum of the query values, not just their count.
ghost function Pos(t: int): nat { if t > 0 then t else 0 }

ghost function SumPos(s: seq<int>, from: nat, upto: nat): nat
  requires from <= upto <= |s|
  decreases upto - from
{
  if from == upto then 0 else Pos(s[from]) + SumPos(s, from + 1, upto)
}

lemma SumPosSnoc(s: seq<int>, upto: nat)
  requires upto < |s|
  ensures SumPos(s, 0, upto + 1) == SumPos(s, 0, upto) + Pos(s[upto])
{
  SumPosSnocFrom(s, 0, upto);
}

lemma SumPosSnocFrom(s: seq<int>, from: nat, upto: nat)
  requires from <= upto < |s|
  ensures SumPos(s, from, upto + 1) == SumPos(s, from, upto) + Pos(s[upto])
  decreases upto - from
{
  if from == upto {
  } else {
    SumPosSnocFrom(s, from + 1, upto);
  }
}

lemma ConsecProdNonneg(m: int)
  ensures m * (m + 1) >= 0
{
  if m >= 0 {
  } else {
  }
}

method Solve(n: int, numbers: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires |numbers| >= n
  ensures steps <= 2 + 2 * n * 500001 + 2 * SumPos(numbers, 0, n)
{
  steps := 1;
  var lines: seq<string> := [];
  var qi := 0;
  ghost var lineLenSum: nat := 0;
  while qi < n
    invariant 0 <= qi <= n
    invariant steps <= 1 + qi * 500000 + SumPos(numbers, 0, qi)
    invariant lineLenSum <= qi * 500000 + SumPos(numbers, 0, qi)
    decreases n - qi
  {
    SumPosSnoc(numbers, qi);
    var t := numbers[qi];
    if t == 1 {
      lines := lines + ["1337"];
      lineLenSum := lineLenSum + 4;
      steps := steps + 2;
    } else {
      var lo := 0;
      var hi := 100000;
      ghost var bsteps := steps;
      while lo < hi
        invariant 0 <= lo <= hi <= 100000
        invariant steps <= bsteps + 3 * (100000 - (hi - lo))
        decreases hi - lo
      {
        var mid := (lo + hi) / 2;
        if mid * (mid - 1) / 2 < t {
          lo := mid + 1;
        } else {
          hi := mid;
        }
        steps := steps + 3;
      }
      var x := lo;
      var threes := x - 1 - 2;
      var threesN := if threes < 0 then 0 else threes;
      var aXm1 := (x - 1) * (x - 2) / 2;
      ConsecProdNonneg(x - 2);
      assert (x - 1) * (x - 2) == (x - 2) * (x - 2 + 1);
      assert aXm1 >= 0;
      var ones := t - aXm1;
      var onesN := if ones < 0 then 0 else ones;
      assert onesN <= Pos(t);
      var ans := "1" + Repeat("3", threesN) + Repeat("1", onesN) + "337";
      steps := steps + threesN + onesN + 4;
      lineLenSum := lineLenSum + threesN + onesN + 4;
      lines := lines + [ans];
      steps := steps + 1;
    }
    qi := qi + 1;
  }
  assert qi == n;
  assert lineLenSum <= n * 500000 + SumPos(numbers, 0, n);
  output := Join(lines, "\n");
  steps := steps + lineLenSum + n + 1;
}
