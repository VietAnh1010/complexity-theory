// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : other
//   cause          : both
//   confidence     : high
//   auditor        : labelaudit-batch-08
//
//   The Python does not match the label AND the translation diverges
//   from the Python. Both need attention.
//
//   evidence:
//     ReverseString1345(s) = ReverseString1345(s[1..]) + [s[0]]
//     concatenates a growing accumulator at every one of n recursion
//     levels, exactly the ReverseSeq/888_6 pattern, making a single call
//     O(n**2) on a row of length n, and it runs inside a loop of n/2
//     iterations giving O(n**3) overall; Python's `right[i][::-1]` is a
//     single O(n) C-level slice reversal called n/2 times, so Python is
//     O(n**2), not matching the O(n) label either.
//
//   how this label could be wrong, and what to check:
//     The label assumes reversing a row costs O(n). Open ReverseString1345
//     and check its shape: `ReverseString1345(s[1..]) + [s[0]]`
//     concatenates a growing result at every one of |s| recursion levels,
//     which is the same quadratic-recursion pattern documented for
//     ReverseSeq in 888_6, making one call O(n**2), not O(n). It is called
//     `half` = n/2 times in Solve's while loop, so also check that this
//     multiplies out across the whole grid rather than being a one-off
//     call.
//
//   structural facts (deterministic, from labelaudit.py):
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
