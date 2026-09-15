// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-batch-07
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     `s` is computed as floor(sqrt(n)) via `while (s+1)*(s+1)<=n`, and
//     `l:=2*s+1` bounds the size of `num0`, `num`, `prevRow` and `row`, so
//     the DP loop `while i<k` nested with `while j<l` costs O(k*sqrt(n)),
//     not O(n*m) (real class O(k*sqrt(n))); the Python's `s=int(n**0.5)`
//     builds the identical sqrt(n)-sized `Num` array, so both share this
//     sub-linear-in-n shape.
//
//   how this label could be wrong, and what to check:
//     The label O(n*m) assumes the loop count scales with N itself. Check
//     `while (s+1)*(s+1) <= n`: it sets s to floor(sqrt(n)), and `l :=
//     2*s+1` sizes every array that follows, so the inner DP loop over j<l
//     runs O(sqrt(n)) times per k, not O(n) times; compare against the
//     Python's identical `s=int(n**0.5)`.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 74, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 2,
//     "loops": 7, "recursive_helpers": 0, "seq_append_read_in_same_loop":
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

method Solve(a: int, b: int) returns (output: string)
{
{

  var n := a;
  var k := b;
  var mod := 1000000007;
  var s := 0;
  while (s+1)*(s+1) <= n
    decreases n - s*s
  {
    s := s + 1;
  }
  var l := 2*s + 1;
  var num0 := new int[l];
  var ii := 0;
  while ii <= s
    decreases s - ii
  {
    num0[ii] := ii;
    ii := ii + 1;
  }
  var tt := 0;
  while tt < s
    decreases s - tt
  {
    num0[s+1+tt] := n / (s - tt);
    tt := tt + 1;
  }
  var num := new int[l];
  num[0] := num0[0];
  var jj := 1;
  while jj < l
    decreases l - jj
  {
    num[jj] := num0[jj] - num0[jj-1];
    jj := jj + 1;
  }

  var prevRow := num;
  var i := 1;
  while i < k
    invariant prevRow.Length == l
    decreases k - i
  {
    var row := new int[l];
    var tmp := 0;
    var j := 1;
    while j < l
      invariant 1 <= j <= l
      invariant row.Length == l
      invariant prevRow.Length == l
      decreases l - j
    {
      tmp := (tmp + prevRow[j]) % mod;
      row[l - j] := (tmp * num[l - j]) % mod;
      j := j + 1;
    }
    prevRow := row;
    i := i + 1;
  }

  var ans := 0;
  var idx := 1;
  while idx < l
    invariant 1 <= idx <= l
    invariant prevRow.Length == l
    decreases l - idx
  {
    ans := (ans + prevRow[idx]) % mod;
    idx := idx + 1;
  }
  output := IntToString(ans);
}
}
