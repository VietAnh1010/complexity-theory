// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(nlogn)
//   audited class  : O(n**2)
//   cause          : translation
//   confidence     : high
//   auditor        : labelaudit-batch-19
//
//   The Python matches its label; the DAFNY does not. The label is right
//   about the program it was measured on and the translation is the
//   defect.
//
//   evidence:
//     s := s[i := s[i-1] + 1] is a seq update executed inside the while
//     loop, potentially on every one of the n-1 iterations (e.g. when all
//     input values are equal), each copying |s|=n elements, giving
//     O(n**2); Python's s[i]=s[i-1]+1 is an O(1) list write so the Python
//     stays O(nlogn) after sorted() as labeled.
//
//   how this label could be wrong, and what to check:
//     The label assumes s[i]=s[i-1]+1 is O(1) as in Python. Open the while
//     i<n loop and confirm the line s := s[i := s[i-1]+1] is a seq update;
//     test the worst case where every a_i is equal (every iteration
//     triggers the update) — if the update fires close to n times, each
//     copying |s|=n elements, the true cost is O(n**2), dominating the
//     O(nlogn) sort.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 45, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 1, "recursive_helpers": 2, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": ["Merge", "Sort", "SortInts"],
//     "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 546_B. Soldier and Badges  (problem 2586, solution 2586_216)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n=int(input())
// ans=0
// s=sorted(list(map(int,input().split())))
// for i in range(1,n):
//     if s[i]<=s[i-1]:
//         ans+=s[i-1]-s[i]+1
//         s[i]=s[i-1]+1
// print(ans)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

lemma MergeLength<T>(a: seq<T>, b: seq<T>, less: (T, T) -> bool)
  ensures |Merge(a, b, less)| == |a| + |b|
  decreases |a| + |b|
{
  if |a| == 0 || |b| == 0 {
  } else if less(b[0], a[0]) {
    MergeLength(a, b[1..], less);
  } else {
    MergeLength(a[1..], b, less);
  }
}

lemma SortLength<T>(s: seq<T>, less: (T, T) -> bool)
  ensures |Sort(s, less)| == |s|
  decreases |s|
{
  if |s| <= 1 {
  } else {
    SortLength(s[..|s| / 2], less);
    SortLength(s[|s| / 2..], less);
    MergeLength(Sort(s[..|s| / 2], less), Sort(s[|s| / 2..], less), less);
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n == |a_list|
  requires n >= 1
{
  SortLength(a_list, (x: int, y: int) => x < y);
  var s := SortInts(a_list);
  var ans := 0;
  var i := 1;
  while i < n
    invariant 1 <= i <= n
    invariant |s| == n
    decreases n - i
  {
    if s[i] <= s[i - 1] {
      ans := ans + s[i - 1] - s[i] + 1;
      s := s[i := s[i - 1] + 1];
    }
    i := i + 1;
  }
  output := IntToString(ans);
}
