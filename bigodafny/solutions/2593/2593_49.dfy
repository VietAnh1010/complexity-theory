// 991_B. Getting an A  (problem 2593, solution 2593_49)
// time complexity: O(n**2)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n = int(input())
// l = list(map(int,input().split()))
// s = sum(l)
// avg = s/n
// if(avg>=4.5):
//     print(0)
// else:
//     req= s-avg
//     l.sort()
//     i=0
//     while(True):
//        dif = 5-l[i]
//        s =s+dif
//        avg = s/n
//        if(avg>=4.5):
//            print(i+1)
//            break
//        i+=1
//        
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, a_list: seq<int>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
