// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n**2)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-10
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     arr := arr[pos := "0"] and arr[pos2 := "1"] each perform a full O(n)
//     seq copy inside two while loops bounded by d and k-d, giving O(n**2)
//     in the Dafny, while Python's number[-i-1]='0' is an O(1) in-place
//     list write making the Python O(n); the label's O(n**2) matches the
//     Dafny only by coincidence.
//
//   how this label could be wrong, and what to check:
//     not recorded by this batch
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 42, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 1,
//     "loops": 2, "recursive_helpers": 0, "seq_append_read_in_same_loop":
//     false, "seq_args": 1, "seq_update_in_loop": true,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 1165_A. Remainder  (problem 1622, solution 1622_305)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
//     n, x, y = map(int, input().split())
//     number = list(input())
//     count = 0
//     i = 0
//     while i < y:
//         if number[-i - 1] != '0':
//             count += 1
//             number[-i - 1] = '0'
//         i += 1
//     i += 1
//     if number[-y - 1] == "0":
//         number[-y -1] = "1"
//         count += 1
//     while i < x:
//         if number[-i - 1] != '0':
//             count += 1
//             number[-i - 1] = '0'
//         i += 1
//     print(count)
// 
// 
// 
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, d: int, binary_list: seq<string>) returns (output: string)
  requires 0 <= d < |binary_list|
  requires k <= |binary_list|
{
  var arr := binary_list;
  var len := |arr|;
  var count := 0;
  var i := 0;
  while i < d
    invariant 0 <= i <= d
    invariant |arr| == len
    decreases d - i
  {
    var pos := len - i - 1;
    if arr[pos] != "0" {
      count := count + 1;
      arr := arr[pos := "0"];
    }
    i := i + 1;
  }
  i := i + 1;
  var pos2 := len - d - 1;
  if arr[pos2] == "0" {
    arr := arr[pos2 := "1"];
    count := count + 1;
  }
  while i < k
    invariant d + 1 <= i
    invariant |arr| == len
    decreases k - i
  {
    var pos3 := len - i - 1;
    if arr[pos3] != "0" {
      count := count + 1;
      arr := arr[pos3 := "0"];
    }
    i := i + 1;
  }
  output := IntToString(count);
}
