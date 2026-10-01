// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-04
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop runs n/2 times and each iteration calls
//     ReverseString1345(board[n-1-i]) on a row of n characters, which
//     costs O(n) by its recursion on s[1..], so the Dafny is O(n**2) in
//     the side length; the Python's right[i][::-1] and the string
//     comparison per row are O(n) each, also O(n**2).
//
//   how this label could be wrong, and what to check:
//     The label O(n) is right only if n counts the total characters of the
//     board. The statement says n lines of n characters each, so the row
//     width equals n; open the Dafny `while i < half` loop and
//     ReverseString1345, and decide whether the dataset's n is the line
//     count (then cost is n*n) or the input length (then the label
//     stands).
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 23, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": [], "loop_depth": 1, "loops": 1,
//     "recursive_helpers": 1, "seq_append_read_in_same_loop": false,
//     "seq_args": 1, "seq_update_in_loop": false, "set_build_in_loop":
//     false, "sorts": [], "uses_map": false, "uses_multiset": false,
//     "uses_set": false}
// --------------------------------------------------------------------

// 462_A. Appleman and Easy Task  (problem 1345, solution 1345_111)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// 
// row = []
// for i in range (n): row.append(input())
// 
// left = row[:n//2+1]
// right = row[n//2:]
// 
// right = right[::-1]
// 
// check = True
// for i in range (n//2):
//     if(right[i][::-1] != left[i]):
//         check = False
//         break
// 
// print('YES' if (check) else 'NO')
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ReverseString1345(s: string): string
  decreases |s|
{
  if |s| == 0 then "" else ReverseString1345(s[1..]) + [s[0]]
}

method Solve(n: int, board: seq<string>) returns (output: string)
  requires n >= 0
  requires n == |board|
{
  var half := n / 2;
  var ok := true;
  var i := 0;
  while i < half
    invariant 0 <= i <= half
    decreases half - i
  {
    if ReverseString1345(board[n-1-i]) != board[i] { ok := false; }
    i := i + 1;
  }
  output := if ok then "YES" else "NO";
}
