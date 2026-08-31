// 1358_D. The Best Vacation  (problem 888, solution 888_6)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n,x=map(int,input().split());D=list(map(int,input().split()));Ans=[];D+=D;D=D[::-1];d=0;p=0;q=0;tot=0;ans=0
// for i in D:Ans.append(i*(i+1)//2)
// while p<2*n and q<2*n:
//     while p<2*n and q<2*n and d+D[p]<x:d+=D[p];tot+=Ans[p];p+=1
//     if p==q:k=D[p]-x+d;tot+=Ans[p]-k*(k+1)//2;ans=max(ans,tot);d=0;tot=0;p+=1;q+=1    
//     elif p<2*n and q<2*n:k=D[p]-x+d;tot+=Ans[p]-k*(k+1)//2;ans=max(ans,tot);d-=min(D[q],d);tot-=Ans[q];tot-=Ans[p]-k*(k+1)//2;q+=1
// print(ans)          
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
