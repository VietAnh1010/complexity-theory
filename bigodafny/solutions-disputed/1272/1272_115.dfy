// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r4-u01
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve pays O(n**2) for the nested loop that reorders by length plus,
//     for each of n-1 adjacent pairs, ContainsFrom1272a walks the haystack
//     positions (O(m) each), so O(n**2 + n*m); the Python's find per pair
//     pays the same string-width term, so a label with only n is
//     incomplete.
//
//   how this label could be wrong, and what to check:
//     The label O(n**2) names only the string count n. The double loop
//     over list1 is O(n**2) by length comparisons, but the check pass runs
//     Contains1272a(list1[k+1], list1[k]) which scans the haystack's
//     characters, a width m term. The claim fails if you consider m
//     negligible against n; the class is O(n**2 + n*m) in the two sizes,
//     and the rule says a cap does not make m constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 64, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 2, "loops":
//     4, "recursive_helpers": 2, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": true, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 988_B. Substrings Sort  (problem 1272, solution 1272_115)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// list1=[]
// for i in range(n):
//     s=input()
//     list1.append(s)
// # list1.sort()
// for i in range(n-1):
//     for j in range(i,n):
//         if(len(list1[i])>len(list1[j])):
//             list1[i],list1[j]=list1[j],list1[i]
// f=0
// for i in range(n-1):
//     # if(list1[i] in list1[i+1]):
//     x=list1[i+1].find(list1[i])
//     if(x>=0):
//         continue
//     else:
//         f=1
// if(f==0):
//     print("YES")
//     for i in range(n):
//         print(list1[i])
// else:
//     print("NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ContainsFrom1272a(hay: string, needle: string, pos: nat): bool
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  if pos + |needle| > |hay| then false
  else if hay[pos..pos+|needle|] == needle then true
  else ContainsFrom1272a(hay, needle, pos + 1)
}

function Contains1272a(hay: string, needle: string): bool
{
  |needle| == 0 || ContainsFrom1272a(hay, needle, 0)
}

method Solve(n: int, strings: seq<string>) returns (output: string)
  requires n == |strings|
{
  var list1 := strings;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n
    invariant |list1| == n
    decreases n - 1 - i
  {
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant |list1| == n
      decreases n - j
    {
      if |list1[i]| > |list1[j]| {
        var tmp := list1[i];
        list1 := list1[i := list1[j]][j := tmp];
      }
      j := j + 1;
    }
    i := i + 1;
  }
  var f := 0;
  var k := 0;
  while k < n - 1
    invariant 0 <= k <= n
    invariant |list1| == n
    decreases n - 1 - k
  {
    if !Contains1272a(list1[k+1], list1[k]) { f := 1; }
    k := k + 1;
  }
  if f == 0 {
    var lines: seq<string> := ["YES"];
    var m := 0;
    while m < n
      invariant 0 <= m <= n
      decreases n - m
    {
      lines := lines + [list1[m]];
      m := m + 1;
    }
    output := Join(lines, "\n");
  } else {
    output := "NO";
  }
}
