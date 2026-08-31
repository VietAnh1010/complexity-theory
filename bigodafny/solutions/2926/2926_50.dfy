// 66_D. Petya and His Friends  (problem 2926, solution 2926_50)
// time complexity: O(n)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// l=[2	,3	,5	,7	,11	,13	,17	,19	,23	,29	,31	,37	,41	,43	,47	,53	,59	,61	,67	,71
// ,73	,79	,83	,89	,97	,101	,103	,107	,109	,113	,127	,131	,137	,139	,149	,151	,157	,163	,167	,173
// ,179	,181	,191	,193	,197	,199	,211	,223	,227	,229	,233	,239	,241]
// n=int(input())
// l1=[1 for i in range(n)]
// if n==2 :
//     print("-1")
//     exit()
// for i in range(n-1) :
//     l1[i]=2*l[i+1]
//     l1[-1]*=l[i+1]
// for x in l1 :
//     print(x)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
