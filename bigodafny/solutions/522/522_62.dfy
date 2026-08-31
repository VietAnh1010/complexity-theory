// p00021 Parallelism  (problem 522, solution 522_62)
// time complexity: O(n*m)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N = int(input())
// for _ in range(N):
//     P = list(map(float,input().split()))
//     a, b, c, d = [complex(P[i*2],P[i*2+1])*1000000 for i in range(4)] 
//     parallel = ((a-b).conjugate() *(c-d)).imag ==0
//     print("YES" if parallel else "NO")
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, points_list: seq<seq<real>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
