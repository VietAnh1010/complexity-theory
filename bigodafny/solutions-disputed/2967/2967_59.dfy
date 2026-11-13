// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : low
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops from max(1, p - k) to min(n, p + k), at most 2k + 1
//     pages, and the Python loops the full `range(p-k, p+k+1)`, so both
//     cost O(k) in the single value k.
//
//   how this label could be wrong, and what to check:
//     The label sums two sizes, but the only loop runs over `range(p-k,
//     p+k+1)`, 2k + 1 iterations in the value k; n only clips the range,
//     and k <= n by the statement. Check that no loop runs to n; the class
//     is linear in k (written O(n) with n = k).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 29, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "ParseInt"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 3,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 399_A. Pages  (problem 2967, solution 2967_59)
// time complexity: O(n+m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,p,k=map(int,input().split(" "))
// ans=""
// if p-k>1:
//     ans+='<< '
// for i in range(p-k, p+k+1):
//     if i>0 and i<=n:
//         if i==p:
//             ans+='('+str(p)+') '
//         else:
//             ans+=str(i)+' '
// if p+k<n:
//     ans+='>>'
// if ans[len(ans)-1]==" ":
//     print(ans[0:len(ans)-1])
// else:
//     print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(v_0: string, v_1: string, v_2: string) returns (output: string)
{
  var n := ParseInt(v_0);
  var p := ParseInt(v_1);
  var k := ParseInt(v_2);
  var tokens: seq<string> := [];
  if p - k > 1 {
    tokens := tokens + ["<<"];
  }
  var lo := if p - k < 1 then 1 else p - k;
  var top := if p + k > n then n else p + k;
  var i := lo;
  while i <= top
    decreases top - i
  {
    if i == p {
      tokens := tokens + ["(" + IntToString(p) + ")"];
    } else {
      tokens := tokens + [IntToString(i)];
    }
    i := i + 1;
  }
  if p + k < n {
    tokens := tokens + [">>"];
  }
  output := Join(tokens, " ") + "\n";
}
