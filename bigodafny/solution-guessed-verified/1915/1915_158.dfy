// 1915_158 (problem 1915) -- blind-arm attempt, run pilot1
//
// The agent that wrote this never saw the complexity label. It
// committed to a class in writing before attempting the proof.
//
//   predicted class : O(n+m)
//   proved bound    : A * n + 2 * A * m + 2 * A + 20
//   proved class    : O(n*m)
//   agent verdict   : proves
//   reference label : O(n+m)
//   prediction correct against the label: True
//   all gates passed: True
//
// A prediction scored incorrect is not necessarily a misreading: the
// label was measured on the Python and this is the Dafny, and where
// the translation changes the class the two disagree by construction.
//
//   basis for the prediction:
//     Two single passes: n-1 GcdNN calls over n_list, then a scan of m_list;
//     each GcdNN call is O(1) since x_i,p_j are capped at 1e18 by the
//     problem statement (Euclid recursion depth is bounded by that cap, not
//     by n or m).
//
//   agent notes:
//     GcdNN recursion depth bounded by its 2nd arg (GcdDepthBound lemma);
//     capped by 1e18 requires, folded into constant A. IntToString cost
//     bounded via a loose |IntToString(x)|<=x+1 lemma. Verified 8/8, 0
//     errors first try.
//
//   verbatim as the agent wrote it, except the prelude include,
//   rewritten to ../../prelude.dfy so this file verifies here.
// --------------------------------------------------------------------

// example: 1915_158
//
// Your task is in TASK.md. The method is below; the Python it was translated
// from is quoted first.
//
// --- source Python ----------------------------------------------------
// import math
// 
// n,m=[int(i) for i in input().split()]
// x=[int(i) for i in input().split()]
// p=[int(i) for i in input().split()]
// x_2=[]
// for i in range(1,len(x)):
//     x_2.append(x[i]-x[i-1])
// g=x_2[0]
// for i in range(1,len(x_2)):
//     g=math.gcd(g,x_2[i])
// b=False
// for i in range (0,len(p)):
//     if(g%p[i]==0):
//         print('YES')
//         print(x[0],i+1)
//         b=True
//         break
// if(not(b)):     
//     print('NO')
// ----------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function GcdNN(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures GcdNN(a, b) >= 0
  ensures GcdNN(a, b) == Gcd(a, b)
  decreases b
{
  if b == 0 then a else GcdNN(b, a % b)
}

// Mirrors GcdNN's own recursion structure, so it counts the real number of
// recursive calls GcdNN makes.
ghost function GcdDepth(a: int, b: int): nat
  requires a >= 0 && b >= 0
  decreases b
{
  if b == 0 then 0 else 1 + GcdDepth(b, a % b)
}

// The second argument is a natural number that strictly decreases (Dafny's
// `%` for b > 0 gives 0 <= a % b < b, the same fact GcdNN's own `decreases b`
// already relies on), so the recursion depth is bounded by its starting value.
lemma GcdDepthBound(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures GcdDepth(a, b) <= b
  decreases b
{
  if b != 0 {
    GcdDepthBound(b, a % b);
  }
}

// A loose length bound: not tight, but enough to fold IntToString's real
// (digit-count) cost into a bound on the value being printed.
lemma IntToStringLenBound(x: int)
  requires x >= 0
  ensures |IntToString(x)| <= x + 1
  decreases x
{
  if x >= 10 { IntToStringLenBound(x / 10); }
}

// Generous fixed constant: covers GcdNN's real cost (bounded by the 10^18
// value cap via GcdDepthBound) and IntToString's real cost (bounded by
// IntToStringLenBound). Any large enough numeral works -- constants are free.
ghost const A: nat := 3000000000000000000

method Solve(n: int, m: int, n_list: seq<int>, m_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 2
  requires m >= 0
  requires |n_list| >= n
  requires |m_list| >= m
  requires forall t :: 0 <= t < |m_list| ==> m_list[t] >= 1
  // Problem statement: 1 <= x_i <= 10^18. GcdNN's real cost per call is
  // proportional to its second argument (GcdDepth above), which here is a
  // difference of two such values -- bounded by the cap, not by n or m.
  requires forall t :: 0 <= t < n ==> 1 <= n_list[t] <= 1000000000000000000
  ensures steps <= A * n + 2 * A * m + 2 * A + 20
{
  steps := 1;
  var g := AbsInt(n_list[1] - n_list[0]);
  steps := steps + A + 5;
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant g >= 0
    invariant steps <= A * (i - 2) + A + 10
    decreases n - i
  {
    ghost var diff := AbsInt(n_list[i] - n_list[i - 1]);
    assert 0 <= diff <= 1000000000000000000;
    GcdDepthBound(g, diff);
    g := GcdNN(g, AbsInt(n_list[i] - n_list[i - 1]));
    steps := steps + A;
    i := i + 1;
  }
  var found := false;
  var idx := 0;
  var j := 0;
  while j < m && !found
    invariant 0 <= j <= m
    invariant steps <= A * (i - 2) + A + 10 + A * j
    decreases m - j
  {
    if g % m_list[j] == 0 {
      found := true;
      idx := j;
    }
    steps := steps + A;
    j := j + 1;
  }
  if found {
    IntToStringLenBound(n_list[0]);
    IntToStringLenBound(idx + 1);
    output := "YES\n" + IntToString(n_list[0]) + " " + IntToString(idx + 1);
    steps := steps + A * (m + 3);
  } else {
    output := "NO";
    steps := steps + A * (m + 3);
  }
}
