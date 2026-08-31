// 1395_A. Boboniu Likes to Color Balls  (problem 1235, solution 1235_318)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// testcases = int(input())
// 
// for i in range(testcases):
//     l = list(map(int , input().split()))
//     odd = 0
//     for i in l:
//         if(i%2 != 0):
//             odd+=1 
//     if(odd in (0,1,4)) or (odd == 3 and (0 not in (l[0],l[1],l[2]))):
//         print("Yes")
//     else:
//         print("No")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, matrix: seq<seq<int>>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < n
    decreases n - i
  {
    var l := matrix[i];
    var odd := 0;
    var j := 0;
    while j < |l|
      decreases |l| - j
    {
      if l[j] % 2 != 0 { odd := odd + 1; }
      j := j + 1;
    }
    var cond1 := odd == 0 || odd == 1 || odd == 4;
    var cond2 := odd == 3 && l[0] != 0 && l[1] != 0 && l[2] != 0;
    if cond1 || cond2 {
      lines := lines + ["Yes"];
    } else {
      lines := lines + ["No"];
    }
    i := i + 1;
  }
  output := Join(lines, "\n");
}
