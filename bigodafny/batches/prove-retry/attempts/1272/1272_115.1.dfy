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

ghost function CFCost(hay: string, needle: string, pos: nat): nat
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  if pos + |needle| > |hay| then 2
  else if hay[pos..pos+|needle|] == needle then |needle| + 4
  else |needle| + 4 + CFCost(hay, needle, pos + 1)
}

lemma CFCostBound(hay: string, needle: string, pos: nat)
  requires 1 <= |needle|
  requires pos <= |hay|
  ensures CFCost(hay, needle, pos) <= (|hay| - pos + 1) * (|needle| + 4)
  decreases |hay| - pos
{
  if pos + |needle| <= |hay| && hay[pos..pos+|needle|] != needle {
    CFCostBound(hay, needle, pos + 1);
    CostMulDistrib(|hay| - pos - 1, 1, |hay| - pos, |needle| + 4);
  } else if pos + |needle| <= |hay| {
    CostMulMonoLeft(1, |hay| - pos + 1, |needle| + 4);
  } else {
    CostMulMonoLeft(1, |hay| - pos + 1, |needle| + 4);
  }
}

ghost function ContBound(L: nat): nat { (L + 1) * (L + 4) }

lemma ContainsCostBound(hay: string, needle: string, L: nat)
  requires |hay| <= L && |needle| <= L
  ensures (if |needle| == 0 then 2 else CFCostOrZero(hay, needle) + 2) <= ContBound(L) + 2
{
  if |needle| >= 1 {
    CFCostBound(hay, needle, 0);
    CostMulMonoLeft(|hay| + 1, L + 1, |needle| + 4);
    CostMulMono(L + 1, |needle| + 4, L + 4);
  }
}

ghost function CFCostOrZero(hay: string, needle: string): nat
{
  if |needle| == 0 then 0 else CFCost(hay, needle, 0)
}

ghost function MaxLen(s: seq<string>): nat
  decreases |s|
{
  if |s| == 0 then 0
  else if |s[0]| > MaxLen(s[1..]) then |s[0]| else MaxLen(s[1..])
}

lemma MaxLenBound(s: seq<string>)
  ensures forall k :: 0 <= k < |s| ==> |s[k]| <= MaxLen(s)
  decreases |s|
{
  if |s| > 0 {
    MaxLenBound(s[1..]);
    forall k | 0 <= k < |s| ensures |s[k]| <= MaxLen(s) {
      if k > 0 { assert s[k] == s[1..][k - 1]; }
    }
  }
}

method Solve(n: int, strings: seq<string>) returns (output: string, ghost steps: nat)
  requires n == |strings|
  ensures steps <= n * (10 * n + 4) + n * (ContBound(MaxLen(strings)) + 12) + 2 * n + 20 + |output|
{
  steps := 2;
  ghost var L := MaxLen(strings);
  MaxLenBound(strings);
  var list1 := strings;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n
    invariant |list1| == n
    invariant forall k :: 0 <= k < n ==> |list1[k]| <= L
    invariant steps <= 2 + i * (10 * n + 4)
    decreases n - 1 - i
  {
    ghost var s0 := steps;
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant |list1| == n
      invariant forall k :: 0 <= k < n ==> |list1[k]| <= L
      invariant steps <= s0 + 10 * (j - i)
      decreases n - j
    {
      if |list1[i]| > |list1[j]| {
        var tmp := list1[i];
        list1 := list1[i := list1[j]][j := tmp];
      }
      steps := steps + 10;
      j := j + 1;
    }
    CostMulDistrib(i, 1, i + 1, 10 * n + 4);
    steps := steps + 4;
    i := i + 1;
  }
  var f := 0;
  var k := 0;
  while k < n - 1
    invariant 0 <= k <= n
    invariant |list1| == n
    invariant forall q :: 0 <= q < n ==> |list1[q]| <= L
    invariant steps <= 2 + n * (10 * n + 4) + k * (ContBound(L) + 12)
    decreases n - 1 - k
  {
    ContainsCostBound(list1[k+1], list1[k], L);
    steps := steps + (CFCostOrZero(list1[k+1], list1[k]) + 2) + 10;
    if !Contains1272a(list1[k+1], list1[k]) { f := 1; }
    CostMulDistrib(k, 1, k + 1, ContBound(L) + 12);
    k := k + 1;
  }
  if f == 0 {
    var lines: seq<string> := ["YES"];
    var m := 0;
    while m < n
      invariant 0 <= m <= n
      invariant |lines| == m + 1
      invariant steps <= 2 + n * (10 * n + 4) + n * (ContBound(L) + 12) + 3 * m
      decreases n - m
    {
      steps := steps + 3;
      lines := lines + [list1[m]];
      m := m + 1;
    }
    output := Join(lines, "\n");
    JoinLen(lines, "\n");
    steps := steps + SumLen(lines) + |lines|;
  } else {
    output := "NO";
  }
}
