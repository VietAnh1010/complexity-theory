// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n*m)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-05
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve runs a loop of n-2 iterations each calling Gcd(nd, diff),
//     costing O(log of the values), followed by a separate loop over m
//     with an early break, so the cost is O(n log max + m), not a product.
//     The Python's nod() runs the same Euclid loop in one for over n and a
//     separate for over m, so the label is wrong for both.
//
//   how this label could be wrong, and what to check:
//     The label assumes nested loops over n and m. Check the two loops:
//     the first runs n times calling Gcd, the second runs m times
//     independently, with an early break; cost is additive, plus Euclid's
//     depth per Gcd call.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 37, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Gcd", "IntToString"], "loop_depth":
//     1, "loops": 2, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 2,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1155_C. Alarm Clocks Everywhere  (problem 1915, solution 1915_63)
// time complexity: O(n*m)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def nod(a,b):
//     while a*b!=0:
//         if a>b:
//             a%=b
//         else:
//             b%=a
//     return a+b
// n,m=map(int,input().split())
// l=[int(j) for j in input().split()]
// p=[int(j) for j in input().split()]
// 
// nd=l[1]-l[0]
// ans=-1
// for i in range(2,n):
// 
//     nd=nod(nd,l[i]-l[i-1])
//     
// for i in range(m):
//    
//     if nd%p[i]==0:
//         ans=i
//         break
//     
// if ans==-1:
//     print('NO')
// else:
//     print('YES')
//     print(l[0],ans+1)
//     
// 
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, n_list: seq<int>, m_list: seq<int>) returns (output: string)
  requires n >= 2
  requires m >= 1
  requires |n_list| == n
  requires |m_list| == m
{
  var l := n_list;
  var p := m_list;
  var nd := AbsInt(l[1] - l[0]);
  var i := 2;
  while i < n
    invariant 2 <= i <= n
    invariant nd >= 0
  {
    nd := AbsInt(Gcd(nd, AbsInt(l[i] - l[i-1])));
    i := i + 1;
  }
  var ans := -1;
  var j := 0;
  while j < m
    invariant 0 <= j <= m
    invariant ans == -1 || (0 <= ans < j)
  {
    if p[j] != 0 && nd % p[j] == 0 {
      ans := j;
      break;
    }
    j := j + 1;
  }
  if ans == -1 {
    output := "NO\n";
  } else {
    output := "YES\n" + IntToString(l[0]) + " " + IntToString(ans+1) + "\n";
  }
}
