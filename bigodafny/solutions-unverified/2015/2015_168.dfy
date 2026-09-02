// 463_B. Caisa and Pylons  (problem 2015, solution 2015_168)
// time complexity: O(n+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// "Codeforces Round #339 (Div. 2)"
// "B. Gena's Code"
// # y=int(input())
// # # a=list(map(int,input().split()))
// # a=list(input().split())
// # nz=0
// # nb=''
// # z=0
// # # print(len(str(z)))
// # for i in a:
// #     if i=='0':
// #         z=1
// #         break
// #     else:
// #         s='1'
// #         l=(len(i)-1)
// #         qz='0'*l
// #         s+=qz
// #         if s==i:
// #             nz+=l
// #         else:
// #             nb=i
// # if nb=='':
// #     nb='1'            
// # ans=nb+('0'*nz)
// # if z==1:
// #     ans='0'
// # print(ans)                
// "Codeforces Round #177 (Div. 2)"
// "B. Polo the Penguin and Matrix"
// # n,m,d=map(int,input().split())
// # a=[]
// # for i in range(n):
// #     b=list(map(int,input().split()))
// #     a.extend(b)
// # a.sort()
// # fa=a[0]
// # f=0
// # c=(a[len(a)//2]-fa)//d
// # moves=0
// # for i in a:
// #     if (i-fa)%d>0:
// #         f=-1
// #     moves+=abs(int((i-fa)/d)-c)
// # if f==-1:
// #     print(-1)
// # else:
// #     print(moves)            
// "Codeforces Round #264 (Div. 2)"
// "B. Caisa and Pylons"
// y=int(input())
// a=list(map(int,input().split()))
// mini=0
// p=-a[0]
// for i in range(1,y):
//     if p<mini:
//         mini=p
//     p=p+a[i-1]-a[i]   
// if p<mini:
//     mini=p    
// if mini<0:
//     print(-1*mini)
// else:
//     print(0)         
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<string>) returns (output: string)
{
  var a := ParseInts(a_list);
  var y := n;
  var mini := 0;
  var p := -a[0];
  var i := 1;
  while i < y
    decreases y - i
  {
    if p < mini {
      mini := p;
    }
    p := p + a[i-1] - a[i];
    i := i + 1;
  }
  if p < mini {
    mini := p;
  }
  if mini < 0 {
    output := IntToString(-1 * mini);
  } else {
    output := "0";
  }
}
