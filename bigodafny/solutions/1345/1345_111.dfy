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
{
  var half := n / 2;
  var ok := true;
  var i := 0;
  while i < half
    decreases half - i
  {
    if ReverseString1345(board[n-1-i]) != board[i] { ok := false; }
    i := i + 1;
  }
  output := if ok then "YES" else "NO";
}
