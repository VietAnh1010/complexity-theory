// 1494_A. ABC String  (problem 1414, solution 1414_23)
// time complexity: O(n**2)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def STR(): return list(input())
// def INT(): return int(input())
// def MAP(): return map(int, input().split())
// def MAP2():return map(float,input().split())
// def LIST(): return list(map(int, input().split()))
// def STRING(): return input()
// import string
// import sys
// from heapq import heappop , heappush, heapify
// from bisect import *
// from collections import deque , Counter , defaultdict
// from math import *
// from itertools import permutations , accumulate
// dx = [-1 , 1 , 0 , 0  ]
// dy = [0 , 0  , 1  , - 1]
// 
// 
// def helper(s):
//     if s[0]==s[-1]:
//         print('NO')
//         return
//     a=[]
//     start=s[0]
//     end=s[-1]
//     flag=0
//     for i in s:
//         if i==start:
//             a.append('(')
//         elif i==end:
//             if len(a)==0:
//                 flag=1
//                 break
//             a.pop()
//         else:
//             a.append('(')
//     if len(a)==0 and flag==0:
//         print('YES')
//         return
//     a=[]
//     for i in s:
//         if i==s[0]:
//             a.append('(')
//         elif i==end:
//             if len(a)==0:
//                 print('NO')
//                 return
//             a.pop()
//         else:
//             if len(a)==0:
//                 print('NO')
//                 return
//             a.pop()
//     if len(a)==0:
//         print('YES')
//     else:
//         print("NO")
// 
// 
// for tt in range(INT()):
//     s=STRING()
//     helper(s)
//     
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, strings: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
