// 462_A. Appleman and Easy Task  (problem 1345, solution 1345_113)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def giveResponse(mat,n):
//     for i in range(1,n+1):
//         for j in range(1,n+1):
//             if (mat[i-1][j] + mat[i+1][j] + mat[i][j-1] + mat[i][j+1])%2==1:
//                 return("NO")
//     return("YES")
// 
// mat=[]
// n = int(input())
// mat = [[0]*(n+2)]
// for i in range(n):
//     sat = [0]
//     for j in (input()):
//         if j=='o':
//             sat.append(1)
//         else:
//             sat.append(0)
//     sat.append(0)
//     mat.append(sat)
// mat.append( [0]*(n+2))
// 
// print(giveResponse(mat,n))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function CellVal1345b(board: seq<string>, n: int, r: int, c: int): int
{
  if r <= 0 || r >= n+1 || c <= 0 || c >= n+1 then 0
  else if 0 <= r-1 < |board| && 0 <= c-1 < |board[r-1]| && board[r-1][c-1] == 'o' then 1 else 0
}

method Solve(n: int, board: seq<string>) returns (output: string)
{
  var ok := true;
  var i := 1;
  while i <= n
    decreases n - i
  {
    var j := 1;
    while j <= n
      decreases n - j
    {
      var s := CellVal1345b(board, n, i-1, j) + CellVal1345b(board, n, i+1, j)
             + CellVal1345b(board, n, i, j-1) + CellVal1345b(board, n, i, j+1);
      if s % 2 == 1 { ok := false; }
      j := j + 1;
    }
    i := i + 1;
  }
  output := if ok then "YES" else "NO";
}
