// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : O(n)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r5-opus
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The Dafny loops i from p - k to p + k emitting one token per page,
//     2k + 1 iterations in the input value k, so the cost is O(k); the
//     Python's single `for` loop over the same range matches.
//
//   how this label could be wrong, and what to check:
//     The label multiplies two sizes, but the only loop runs `range(p-k,
//     p+k+1)`, 2k + 1 iterations in the value k, with no nesting. Check
//     that n and p only bound comparisons; the class is linear in k
//     (written O(n) with n = k).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 30, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "Join", "ParseInt"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 3,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 399_A. Pages  (problem 2967, solution 2967_293)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,p,k = map(int,input().split())
// if((p-k)>1):
//     print("<<",end=" ")
// for i in range(p-k,p+k+1):
//     if(i<1) or (i>n):
//         continue
//     elif(i==p):
//         print("(" + str(i) + ")",end=" ")
//     else:
//         print(str(i),end=" ")
// if((p+k)<n):
//     print(">>")
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
  var i := p - k;
  var hi := p + k;
  while i <= hi
    decreases hi - i
  {
    if i >= 1 && i <= n {
      if i == p {
        tokens := tokens + ["(" + IntToString(i) + ")"];
      } else {
        tokens := tokens + [IntToString(i)];
      }
    }
    i := i + 1;
  }
  if p + k < n {
    tokens := tokens + [">>"];
  }
  output := Join(tokens, " ") + "\n";
}
