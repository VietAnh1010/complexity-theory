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
// 18_D. Seller Bob  (problem 2942, solution 2942_55)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// s=int(input())
// a={}
// sum=[]
// ls=-1
// for i in range(s):
//   sum.append(0)
// for i in range(s):
//   n, z = map(str, input().split())
//   m=int(z)
//   if(n=="win"):
//       a[m]=(1,i)
//   if (n=="sell"):
//     p = a.get(m, -1)
//     if(p!=-1):
//       if(sum[i-1]<2**m+sum[a[m][1]]):
//         sum[i]=2**m+sum[a[m][1]]
//         ls=i
//       else:
//         if(a[m][1]>ls):
//           sum[i]=2**m+sum[i-1]
//           ls=i
//   if(sum[i]==0):
//     sum[i]=sum[i-1]
// print(sum[s-1])
//
// # Sun Mar 24 2019 13:38:31 GMT+0300 (MSK)
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

// The translation keeps the Python's dict (a map, O(1) per access) and
// computes 2**m by squaring, charged its recursion depth: BitLen(m) + 1.
// m is an input VALUE, so the bound carries TokBits, the sum of the
// exponents' bit lengths: O(n log max m), not O(n).

// Pow2_55's recursion depth: one level per halving of e.
ghost function Pow2Depth(e: nat): nat
  decreases e
{
  if e == 0 then 1 else 1 + Pow2Depth(e / 2)
}

lemma Pow2DepthBound(e: nat)
  ensures Pow2Depth(e) <= BitLen(e) + 1
  decreases e
{
  if e > 0 {
    Pow2DepthBound(e / 2);
    assert (e + 2) / 2 == e / 2 + 1;
  }
}

// the bit lengths of the first k transactions' exponents
ghost function TokBits(t: seq<seq<string>>, k: nat): nat
  decreases k
{
  if k == 0 then 0
  else TokBits(t, k - 1)
       + (if k - 1 < |t| && |t[k - 1]| >= 2 then BitLen(ParseInt(t[k - 1][1])) else 0)
}

method Solve(n: int, transactions: seq<seq<string>>) returns (output: string, ghost steps: nat)
  ensures steps <= 20 * (if n > 0 then n else 0) + TokBits(transactions, if n > 0 then n else 0) + 10
{
  steps := 1;
  var s := n;
  var a: map<int, int> := map[];
  var sums: seq<int> := seq(if s > 0 then s else 0, _ => 0);
  var ls := -1;
  var i := 0;
  steps := steps + 2;
  ghost var base1 := steps;
  while i < s
    invariant 0 <= i
    invariant i <= (if s > 0 then s else 0)
    invariant |sums| == (if s > 0 then s else 0)
    invariant steps <= base1 + 20 * i + TokBits(transactions, i)
    decreases s - i
  {
    ghost var s0 := steps;
    ghost var bits := if i < |transactions| && |transactions[i]| >= 2
                      then BitLen(ParseInt(transactions[i][1])) else 0;
    if i < |transactions| && |transactions[i]| >= 2 {
      var kind := transactions[i][0];
      var m := ParseInt(transactions[i][1]);
      steps := steps + 3;
      if kind == "win" {
        a := a[m := i];
        steps := steps + 1;
      } else if kind == "sell" {
        steps := steps + 1;
        if m in a && m >= 0 {
          var winIdx := a[m];
          // Pow2_55(m) is charged its recursion depth
          Pow2DepthBound(m);
          steps := steps + 1 + Pow2Depth(m);
          var pw := Pow2_55(m);
          var prev := if i == 0 then 0 else sums[i - 1];
          var base := if 0 <= winIdx < |sums| then sums[winIdx] else 0;
          steps := steps + 2;
          if prev < pw + base {
            sums := sums[i := pw + base];
            ls := i;
            steps := steps + 2;
          } else if winIdx > ls {
            var prevSum := if i == 0 then 0 else sums[i - 1];
            sums := sums[i := pw + prevSum];
            ls := i;
            steps := steps + 3;
          }
        }
      }
    }
    if sums[i] == 0 {
      var prevSum2 := if i == 0 then 0 else sums[i - 1];
      sums := sums[i := prevSum2];
      steps := steps + 2;
    }
    i := i + 1;
    steps := steps + 1;
    assert steps <= s0 + 20 + bits;
    assert TokBits(transactions, i) == TokBits(transactions, i - 1) + bits;
  }
  if s > 0 {
    output := IntToString(sums[s - 1]);
  } else {
    output := IntToString(0);
  }
  steps := steps + 2;
}

// 2**e by squaring: depth log e, as Python's ** is one operation
function Pow2_55(e: int): int
  requires e >= 0
  ensures Pow2_55(e) >= 1
  decreases e
{
  if e == 0 then 1
  else
    var h := Pow2_55(e / 2);
    if e % 2 == 0 then h * h else 2 * h * h
}
