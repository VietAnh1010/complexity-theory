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
// 1155_C. Alarm Clocks Everywhere  (problem 1915, solution 1915_158)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
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
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

function GcdNN(a: int, b: int): int
  requires a >= 0 && b >= 0
  ensures GcdNN(a, b) >= 0
  ensures GcdNN(a, b) == Gcd(a, b)
  decreases b
{
  if b == 0 then a else GcdNN(b, a % b)
}

// The bits of the gaps |s[k] - s[k-1]| for 2 <= k < i: what the gcd loop
// reads.
ghost function GapBits(s: seq<int>, i: nat): nat
  requires 2 <= i <= |s|
  decreases i
{
  if i == 2 then 0 else GapBits(s, i - 1) + BitLen(AbsInt(s[i - 1] - s[i - 2]))
}

// Each GcdNN call costs Euclid's recursion depth, GcdSteps (GcdNN recurses
// as Gcd does): at most 2 * BitLen(gap) + 2 (GcdStepsBound).
method Solve(n: int, m: int, n_list: seq<int>, m_list: seq<int>) returns (output: string, ghost steps: nat)
  requires n >= 2
  requires m >= 0
  requires |n_list| >= n
  requires |m_list| >= m
  requires forall t :: 0 <= t < |m_list| ==> m_list[t] >= 1
  ensures steps <= 4 * n + 3 * m + 2 * GapBits(n_list, n) + 6
{
  steps := 1;
  var g := AbsInt(n_list[1] - n_list[0]);
  var i := 2;
  steps := steps + 2;
  while i < n
    invariant 2 <= i <= n
    invariant g >= 0
    invariant steps <= 4 * (i - 2) + 3 + 2 * GapBits(n_list, i)
    decreases n - i
  {
    GcdStepsBound(g, AbsInt(n_list[i] - n_list[i - 1]));
    steps := steps + 2 + GcdSteps(g, AbsInt(n_list[i] - n_list[i - 1]));
    g := GcdNN(g, AbsInt(n_list[i] - n_list[i - 1]));
    i := i + 1;
  }
  var found := false;
  var idx := 0;
  var j := 0;
  steps := steps + 1;
  while j < m && !found
    invariant 0 <= j <= m
    invariant steps <= 4 * n + 2 * GapBits(n_list, n) + 2 * j - 4
    decreases m - j
  {
    if g % m_list[j] == 0 {
      found := true;
      idx := j;
    }
    j := j + 1;
    steps := steps + 2;
  }
  if found {
    output := "YES\n" + IntToString(n_list[0]) + " " + IntToString(idx + 1);
  } else {
    output := "NO";
  }
  steps := steps + 1;
}
