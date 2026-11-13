// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n)
//   audited class  : O(n**2)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-r4-d02
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     The loop runs n/2 times and each iteration calls
//     ReverseString1345(board[n-1-i]), a recursion over a row of n
//     characters, then compares it with board[i]; with an n x n board that
//     is O(n**2). The Python does right[i][::-1] != left[i] on the same
//     rows, so it is quadratic as well and the label is wrong.
//
//   how this label could be wrong, and what to check:
//     The label counts the n rows only, but each row is itself n
//     characters long. Check ReverseString1345 inside the `while i < half`
//     loop: it reverses a whole row (length n), so each of n/2 iterations
//     costs O(n).
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

lemma SumLenCat(a: seq<string>, b: seq<string>)
  ensures SumLen(a + b) == SumLen(a) + SumLen(b)
  decreases |a|
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert (a + b)[0] == a[0];
    assert (a + b)[1..] == a[1..] + b;
    SumLenCat(a[1..], b);
  }
}

method Solve(n: int, board: seq<string>) returns (output: string, ghost steps: nat)
  requires n >= 0
  requires n == |board|
  ensures steps <= 4 * n + 2 * SumLen(board) + 4
{
  steps := 3;
  var half := n / 2;
  var ok := true;
  var i := 0;
  while i < half
    invariant 0 <= i <= half
    invariant half <= n - half
    invariant steps <= 3 + 8 * i + 2 * SumLen(board[n - i..])
    decreases half - i
  {
    if ReverseString1345(board[n-1-i]) != board[i] { ok := false; }
    assert board[n-1-i..] == [board[n-1-i]] + board[n-i..];
    SumLenCat([board[n-1-i]], board[n-i..]);
    assert SumLen([board[n-1-i]]) == |board[n-1-i]|;
    steps := steps + 8 + 2 * |board[n-1-i]|;
    i := i + 1;
  }
  assert board == board[..n-i] + board[n-i..];
  SumLenCat(board[..n-i], board[n-i..]);
  output := if ok then "YES" else "NO";
  steps := steps + 1;
}
