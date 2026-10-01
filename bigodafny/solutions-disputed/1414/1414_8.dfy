// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n*m)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve loops over |strings| and each SolveOne call makes two linear
//     passes over its string a, with SortInts([cntA, cntB, cntC]) on three
//     counters, so n strings each scanned is O(n*m) under the naming rule,
//     not O(n). The Python solve() also loops range(n) per string, so the
//     label names the wrong sizes.
//
//   how this label could be wrong, and what to check:
//     The label treats n as one size, but Solve receives n separate
//     strings. Check SolveOne: each call scans its own string a (`while i
//     < m`, `while j < m`), so the cost is the number of strings times
//     their length; the 3-element SortInts is constant.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 75, "data_dependent_loops": 1, "decreases_star":
//     false, "linear_prelude_calls": ["Join"], "loop_depth": 1, "loops":
//     3, "recursive_helpers": 1, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": ["SortInts"], "uses_map": false, "uses_multiset":
//     false, "uses_set": false}
// --------------------------------------------------------------------

// 1494_A. ABC String  (problem 1414, solution 1414_8)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def solve(n, a):
//     cnt = {"A": 0, "B": 0, "C": 0}
//     for i in range(n):
//         cnt[a[i]] += 1
//     vs = sorted(cnt.values())
//     if vs[0] + vs[1] != vs[2]:
//         return False
//     first = a[0]
//     last = a[-1]
//     if first == last:
//         return False
//     other = first
//     if cnt[first] == vs[2]:
//         other = last
//     num_open = 0
//     for i in range(n):
//         if a[i] == first:
//             num_open += 1
//         elif a[i] == last:
//             num_open -= 1
//         elif other == first:
//             num_open += 1
//         else:
//             num_open -= 1
//         if num_open < 0:
//             return False
//     return num_open == 0
// 
// def main():
//     t = int(input())
//     for _ in range(t):
//         a = input(); n = len(a)
//         if solve(n, a):
//             print("YES")
//         else:
//             print("NO")
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method SolveOne(a: string) returns (ok: bool)
{
  var m := |a|;
  var cntA := 0;
  var cntB := 0;
  var cntC := 0;
  var i := 0;
  while i < m
    invariant 0 <= i <= m
    decreases m - i
  {
    if a[i] == 'A' { cntA := cntA + 1; }
    else if a[i] == 'B' { cntB := cntB + 1; }
    else if a[i] == 'C' { cntC := cntC + 1; }
    i := i + 1;
  }
  var vs := SortInts([cntA, cntB, cntC]);
  if vs[0] + vs[1] != vs[2] {
    ok := false;
    return;
  }
  if m == 0 {
    ok := false;
    return;
  }
  var first := a[0];
  var last := a[m - 1];
  if first == last {
    ok := false;
    return;
  }
  var other := first;
  var cntFirst := if first == 'A' then cntA else if first == 'B' then cntB else cntC;
  if cntFirst == vs[2] {
    other := last;
  }
  var numOpen := 0;
  var j := 0;
  var failed := false;
  while j < m && !failed
    invariant 0 <= j <= m
    decreases m - j
  {
    if a[j] == first {
      numOpen := numOpen + 1;
    } else if a[j] == last {
      numOpen := numOpen - 1;
    } else if other == first {
      numOpen := numOpen + 1;
    } else {
      numOpen := numOpen - 1;
    }
    if numOpen < 0 {
      failed := true;
    }
    j := j + 1;
  }
  ok := !failed && numOpen == 0;
}

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  var parts: seq<string> := [];
  var i := 0;
  while i < |strings|
    invariant 0 <= i <= |strings|
    decreases |strings| - i
  {
    var ok := SolveOne(strings[i]);
    parts := parts + [if ok then "YES\n" else "NO\n"];
    i := i + 1;
  }
  output := Join(parts, "");
}
