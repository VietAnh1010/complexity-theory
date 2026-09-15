// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(n+mlogm)
//   audited class  : O(n)
//   cause          : label
//   confidence     : high
//   auditor        : labelaudit-batch-15
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Solve has a single while loop over i from 1 to y=n with O(1) body
//     work per iteration (ParseInts and IntToString each cost O(length)
//     once, outside the loop), and the Python mirrors this with one for
//     loop over range(1,y) and no sort call anywhere.
//
//   how this label could be wrong, and what to check:
//     The label posits a second dimension m with a sort, but Solve takes
//     only n and a_list. Check the Dafny body for any Sort/SortInts call
//     or a second sequence parameter; there is none, and the Python
//     for-loop over range(1,y) has no sort either, so a single-dimension
//     linear label is the correct one.
//
//   structural facts (deterministic, from labelaudit.py):
//     {"body_lines": 30, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString", "ParseInts"],
//     "loop_depth": 1, "loops": 1, "recursive_helpers": 0,
//     "seq_append_read_in_same_loop": false, "seq_args": 1,
//     "seq_update_in_loop": false, "set_build_in_loop": false, "sorts":
//     [], "uses_map": false, "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

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
  requires n >= 1
  requires n <= |a_list|
{
  var a := ParseInts(a_list);
  var y := n;
  var mini := 0;
  var p := -a[0];
  var i := 1;
  while i < y
    invariant 1 <= i
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
