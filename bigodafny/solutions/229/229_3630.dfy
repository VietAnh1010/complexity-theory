// 677_A. Vanya and Fence  (problem 229, solution 229_3630)
// time complexity: O(n+mlogm)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// '''
// import math
// 
// def BearAndBigBrother():
//     a, b = map(int, input().split(' '))
//     year = 0
//     while 1:
//         if a > b:
//             break
//         else:
//             a *= 3
//             b *= 2
//             year += 1
//     print(year)
//     return None
// 
// def Tram():
//     n = int(input())
//     p = [0]
//     for i in range(1, n+1):
//         a, b = map(int, input().split())
//         tmp = p[i-1]
//         tmp -= a
//         tmp += b
//         p.append(tmp)
//     print(max(p))
//     return None
// 
// 
// def WrongSubtraction():
//     n ,k = map(int, input().split())
//     for i in range(k):
//         if n % 10 == 0:
//             n = n // 10
//         else:
//             n -= 1
//     print(n)
//     return None
// 
// 
// def Elephant():
//     x = int(input())
//     i = steps = 0
//     tmp = [j for j in range(1, 6) if x // j > 0]
//     stepsize = max(tmp)
//     while i < x:
//         steps += (x-i) // stepsize
//         i += stepsize*steps
//         tmp2 = [j for j in range(1, stepsize) if (x-i) // j > 0]
//         try:
//             stepsize = max(tmp2)
//         except:
//             continue
//     print(steps)
// 
//     return None
// 
// 
// def QueueAtTheSchool():
//     n, t = map(int, input().split())
//     s = input()
//     Q = [i for i in s]
//     for i in range(t):
//         j = 0
//         while j < len(Q)-1:
//             if Q[j] == 'B' and Q[j+1] == 'G':
//                 Q[j], Q[j+1] = Q[j+1], Q[j]
//                 j += 2
//             else:
//                 j += 1
//     s_f = ''.join(Q)
//     print(s_f)
// 
//     return None
// 
// 
// def NearlyLuckyNumber():
//     n = input()
//     nl = str(n.count('4') + n.count('7'))
//     tmp = set([i for i in nl])
//     if (len(tmp) <= 2) and (('4' in tmp) or ('7' in tmp)):
//         print('YES')
//     else:
//         print('NO')
//         
// def Word():
//     s = input()
//     countA = countB = 0
//     for i in s:
//         if i.isupper():
//             countA += 1
//         else:
//             countB += 1
//     if countA > countB:
//         print(s.upper())
//     else:
//         print(s.lower())
// 
// 
// def Translation():
//     s = input()
//     t = input()
//     if s[::-1] == t:
//         print('YES')
//     else:
//         print('NO')
// 
// def AntonAndDanik():
//     n = int(input())
//     s = input()
//     if s.count('A') > s.count('D'):
//         print('Anton')
//     elif s.count('A') < s.count('D'):
//         print('Danik')
//     else:
//         print('Friendship')
//     
// def GeorgeAndAccommodation():
//     n = int(input())
//     count = 0
//     for i in range(n):
//         p, q = map(int, input().split())
//         if q - p >= 2:
//             count += 1
//     print(count)
// 
// 
// def BeautifulYear():
//     y = int(input())
//     y2 = [i for i in str(y+1)]
//     while len(set(y2)) != len(y2):
//         tmp = int(''.join(y2)) + 1
//         y2 = [i for i in str(tmp)]
//     print(int(''.join(y2)))
//  
// 
// def Presents():
//     n = int(input())
//     presents= {}
//     p = list(map(int, input().split()))
//     for i in range(n):
//         presents[i] = p[i]
//     presents_inv = sorted(presents.items(), key = lambda x: (x[1], x[0]))
//     ans = [i[0]+1 for i in presents_inv]
//     print(*ans)
// '''
// 
// def VanyaAndFence():
//     n, h = map(int, input().split())
//     row = list(map(int, input().split()))
//     t_width = 0
//     for i in range(n):
//         if row[i] <= h:
//             t_width += 1
//         else:
//             t_width += 2
//     print(t_width)
// 
// def main():
//     #BearAndBigBrother()
//     #Tram()
//     #WrongSubtraction()
//     #Elephant()
//     #QueueAtTheSchool()
//     #NearlyLuckyNumber()
//     #Word()
//     #Translation()
//     #AntonAndDanik()
//     #GeorgeAndAccommodation()
//     #BeautifulYear()
//     #Presents()
//     VanyaAndFence()
// 
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, k: int, a_list: seq<int>) returns (output: string)
{
  var tw := 0;
  var i := 0;
  while i < n
    decreases n - i
  {
    if a_list[i] <= k {
      tw := tw + 1;
    } else {
      tw := tw + 2;
    }
    i := i + 1;
  }
  output := IntToString(tw);
}
