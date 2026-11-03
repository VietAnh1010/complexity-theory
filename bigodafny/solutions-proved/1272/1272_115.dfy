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

function ContainsFrom1272a(hay: string, needle: string, pos: nat): bool
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  if pos + |needle| > |hay| then
    false
  else if hay[pos .. pos + |needle|] == needle then
    true
  else
    ContainsFrom1272a(hay, needle, pos + 1)
}

ghost function ContainsFrom1272a_steps(hay: string, needle: string, pos: nat): nat
  requires 1 <= |needle|
  requires pos <= |hay|
  decreases |hay| - pos
{
  5 + if pos + |needle| > |hay| then 0 else 5 + if hay[pos .. pos + |needle|] == needle then 0 else 1 + ContainsFrom1272a_steps(hay, needle, pos + 1)
}

function Contains1272a(hay: string, needle: string): bool
{
  |needle| == 0 || ContainsFrom1272a(hay, needle, 0)
}

ghost function Contains1272a_steps(hay: string, needle: string): nat
{
  3 + if |needle| == 0 then 0 else ContainsFrom1272a_steps(hay, needle, 0)
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

lemma CFBound1272a(h: string, nl: string, pos: nat)
  requires 1 <= |nl| && pos <= |h|
  ensures ContainsFrom1272a_steps(h, nl, pos) <= 11 * (|h| - pos + 1)
  decreases |h| - pos
{
  if pos + |nl| > |h| {
  } else if h[pos..pos+|nl|] == nl {
  } else {
    CFBound1272a(h, nl, pos + 1);
  }
}

lemma CBound1272a(h: string, nl: string, L: nat)
  requires |h| <= L
  ensures Contains1272a_steps(h, nl) <= 11 * L + 14
{
  if |nl| >= 1 { CFBound1272a(h, nl, 0); }
}

lemma Fin1272a(n: nat, L: nat, K1: nat, K2: nat)
  requires K1 == 13 * n + 5 && K2 == 11 * L + 22
  ensures n * K1 + n * K2 + 6 * n == n * (13 * n + 5) + n * (11 * L + 28)
{
  CostMulDistrib(K2, 6, K2 + 6, n);
}

method Solve(n: int, strings: seq<string>)
    returns (output: string, ghost steps: nat)
  requires n == |strings|
  ensures steps <= n * (13 * n + 5) + n * (11 * MaxLen(strings) + 28) + 10 + |output|
{
  steps := 0;
  ghost var L := MaxLen(strings);
  MaxLenBound(strings);
  ghost var K1: nat := 13 * n + 5;
  ghost var K2: nat := 11 * L + 22;
  var list1 := strings;
  var i := 0;
  while i < n - 1
    invariant 0 <= i <= n
    invariant |list1| == n
    invariant forall k :: 0 <= k < n ==> |list1[k]| <= L
    invariant steps <= i * K1
    decreases n - 1 - i
  {
    steps := steps + 3;
    ghost var s0 := steps;
    var j := i;
    while j < n
      invariant i <= j <= n
      invariant |list1| == n
      invariant forall k :: 0 <= k < n ==> |list1[k]| <= L
      invariant steps <= s0 + 13 * (j - i)
      decreases n - j
    {
      steps := steps + 2;
      steps := steps + 5;
      if |list1[i]| > |list1[j]| {
        steps := steps + 1;
        var tmp := list1[i];
        steps := steps + 3;
        list1 := list1[i := list1[j]][j := tmp];
      }
      steps := steps + 1;
      j := j + 1;
    }
    steps := steps + 1;
    steps := steps + 1;
    CostMulDistrib(i, 1, i + 1, K1);
    i := i + 1;
  }
  CostMulMonoLeft(i, n, K1);
  steps := steps + 2;
  var f := 0;
  var k := 0;
  ghost var B := steps;
  while k < n - 1
    invariant 0 <= k <= n
    invariant |list1| == n
    invariant steps <= B + k * K2
    invariant B <= n * K1 + 2
    decreases n - 1 - k
  {
    steps := steps + 3;
    CBound1272a(list1[k + 1], list1[k], L);
    steps := steps + (4 + Contains1272a_steps(list1[k + 1], list1[k]));
    if !Contains1272a(list1[k + 1], list1[k]) {
      f := 1;
    }
    steps := steps + 1;
    CostMulDistrib(k, 1, k + 1, K2);
    k := k + 1;
  }
  CostMulMonoLeft(k, n, K2);
  Fin1272a(n, L, K1, K2);
  steps := steps + 2;
  steps := steps + 1;
  if f == 0 {
    steps := steps + 1;
    var lines: seq<string> := ["YES"];
    var m := 0;
    while m < n
      invariant 0 <= m <= n
      invariant |lines| == m + 1
      invariant steps <= n * K1 + n * K2 + 6 + 6 * m
      decreases n - m
    {
      steps := steps + 2;
      steps := steps + (2 + |[list1[m]]|);
      lines := lines + [list1[m]];
      steps := steps + 1;
      m := m + 1;
    }
    steps := steps + 1;
    steps := steps + (SumLen(lines) + |lines|);
    JoinLen(lines, "\n");
    output := Join(lines, "\n");
  } else {
    output := "NO";
  }
}

import opened Prelude
