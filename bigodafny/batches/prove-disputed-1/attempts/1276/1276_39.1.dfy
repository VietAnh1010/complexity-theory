// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny computes `s := ISqrt(n)`, sets `l := 2*s + 1`, and fills k
//     - 1 DP rows of length l, so the cost is O(k sqrt n) in the two input
//     values; the Python's DP has the same shape.
//
//   how this label could be wrong, and what to check:
//     The label multiplies the two input values n and k, but the DP rows
//     have length l = 2*sqrt(n) + 1, not n. Check `s=int(n**0.5)` and
//     `l=len(Num)` in the Python (`l := 2*s + 1` in the Dafny); k rows of
//     sqrt(n) cells give O(k sqrt n).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 69, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 6, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// p02992 AtCoder Beginner Contest 132 - Small Products  (problem 1276, solution 1276_39)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// mod=1000000007
// n,k=map(int,input().split())
// s=int(n**0.5)
// Num=[0]*(s+1)
// for i in range(s,0,-1):
//     Num[i]=i
//     Num.append(n//i)
// l=len(Num)
// for i in range(1,l):
//     Num[-i]=Num[-i]-Num[-i-1]
// DP=[[0]*l for _ in range(k)]
// DP[0]=Num[:]
// for i in range(1,k):
//     tmp=0
//     for j in range(1,l):
//         tmp+=DP[i-1][j]
//         tmp%=mod
//         DP[i][-j]=(tmp*Num[-j])%mod
// ans=0
// for i in DP[-1][1:]:
//     ans+=i
//     ans%=mod
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int) returns (output: string, ghost steps: nat)
  ensures steps <= ISqrtSteps(a) + 40 * (ISqrt(a) + 1) + (if b > 0 then b else 0) * (24 * ISqrt(a) + 16) + |output|
{
{

  var n := a;
  var k := b;
  var mod := 1000000007;
  var s := ISqrt(n);
  var l := 2*s + 1;
  steps := 1 + ISqrtSteps(n) + 3 * l;
  var num0 := new int[l];
  var ii := 0;
  while ii <= s
    invariant 0 <= ii <= s + 1
    invariant num0.Length == l
    invariant steps == 1 + ISqrtSteps(n) + 3 * l + 4 * ii
    decreases s - ii
  {
    num0[ii] := ii;
    ii := ii + 1;
    steps := steps + 4;
  }
  var tt := 0;
  while tt < s
    invariant 0 <= tt <= s
    invariant num0.Length == l
    invariant steps == 1 + ISqrtSteps(n) + 3 * l + 4 * (s + 1) + 6 * tt
    decreases s - tt
  {
    num0[s+1+tt] := n / (s - tt);
    tt := tt + 1;
    steps := steps + 6;
  }
  var num := new int[l];
  num[0] := num0[0];
  var jj := 1;
  while jj < l
    invariant 1 <= jj <= l
    invariant num.Length == l
    invariant num0.Length == l
    invariant steps == 1 + ISqrtSteps(n) + 3 * l + 4 * (s + 1) + 6 * s + 6 * (jj - 1)
    decreases l - jj
  {
    num[jj] := num0[jj] - num0[jj-1];
    jj := jj + 1;
    steps := steps + 6;
  }
  ghost var base := steps;
  ghost var it: nat := 0;
  ghost var K: nat := 12 * l + 4;
  var prevRow := num;
  var i := 1;
  while i < k
    invariant prevRow.Length == l
    invariant num.Length == l
    invariant 1 <= i
    invariant it == i - 1
    invariant steps <= base + it * K
    decreases k - i
  {
    ghost var b0 := steps;
    var row := new int[l];
    steps := steps + l;
    var tmp := 0;
    var j := 1;
    while j < l
      invariant 1 <= j <= l
      invariant row.Length == l
      invariant prevRow.Length == l
      invariant steps == b0 + l + 10 * (j - 1)
      decreases l - j
    {
      tmp := (tmp + prevRow[j]) % mod;
      row[l - j] := (tmp * num[l - j]) % mod;
      j := j + 1;
      steps := steps + 10;
    }
    prevRow := row;
    i := i + 1;
    steps := steps + 4;
    CostMulDistrib(it, 1, it + 1, K);
    it := it + 1;
  }

  var ans := 0;
  var idx := 1;
  ghost var b1 := steps;
  while idx < l
    invariant 1 <= idx <= l
    invariant prevRow.Length == l
    invariant steps == b1 + 6 * (idx - 1)
    decreases l - idx
  {
    ans := (ans + prevRow[idx]) % mod;
    idx := idx + 1;
    steps := steps + 6;
  }
  output := IntToString(ans);
  IntToStringDigits(ans);
  steps := steps + Digits(ans);
  ghost var kk: nat := if k > 0 then k else 0;
  assert it <= kk;
  CostMulMonoLeft(it, kk, K);
  CostMulMono(kk, 12 * l + 4, 24 * s + 16);
}
}
