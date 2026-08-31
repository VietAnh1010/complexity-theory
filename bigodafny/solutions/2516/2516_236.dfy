// 1271_B. Blocks  (problem 2516, solution 2516_236)
// time complexity: O(nlogn)
// python exact-diff baseline: partial
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// # for t in range(int(input())):
// #     s = input()
// #     i, j = 0, 0
// #     cnt = 0
// #     ans = float('inf')
// #     dic = {}
// #     while j < len(s):
// #         if len(dic) < 3:
// #             dic[s[j]] = dic.get(s[j], 0) + 1
// #         # print(j)
// #         # print(dic)
// #         while len(dic) == 3:
// #             ans = min(ans, j - i + 1)
// #             dic[s[i]] -= 1
// #             if dic[s[i]] == 0:
// #                 del dic[s[i]]
// #             i += 1
// #
// #         j += 1
// #     print((0, ans)[ans < float('inf')])
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     s = list(map(int, input().split()))
// #     dp = [1] * n
// #     for i in range(n):
// #         k = 2
// #         while (i + 1) * k <= n:
// #             j = (i + 1) * k
// #             if s[i] < s[j - 1]:
// #                 dp[j - 1] = max(dp[j - 1], dp[i] + 1)
// #             k += 1
// #     print(max(dp))
// 
// 
// # for T in range(int(input())):
// #     t = input()
// #     z, o = 0, 0
// #     for ch in t:
// #         z = z + 1 if ch == '0' else z
// #         o = o + 1 if ch == '1' else o
// #     if z > 0 and o > 0:
// #         print('01' * len(t))
// #     elif o > 0 and not z:
// #         print('1' * len(t))
// #     else:
// #         print('0' * len(t))
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     a.sort()
// #     ans = []
// #     while a:
// #         ans.append(str(a.pop(len(a) // 2)))
// #     print(' '.join(ans))
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     cnt = 0
// #     p = set()
// #     l, r = 0, sum(a)
// #     left, right = {}, {}
// #     for i in a:
// #         right[i] = right.get(i, 0) + 1
// #     for i in range(n - 1):
// #         l += a[i]
// #         left[a[i]] = left.get(a[i], 0) + 1
// #         r -= a[i]
// #         right[a[i]] = right.get(a[i], 0) - 1
// #         if not right[a[i]]:
// #             del right[a[i]]
// #         j = n - i - 1
// #         if (2 + i) * (i + 1) // 2 == l and (j + 1) * j // 2 == r:
// #             if len(left) == i + 1 and len(right) == j:
// #                 cnt += 1
// #                 p.add((i + 1, n - i - 1))
// #     print(cnt)
// #     if cnt:
// #         for el in p:
// #             print(*el)
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     G = []
// #     taken = [False] * n
// #     girl = -1
// #     for i in range(n):
// #         g = list(map(int, input().split()))
// #         k = g[0]
// #         single = True
// #         for j in range(1, k + 1):
// #             if not taken[g[j] - 1]:
// #                 taken[g[j] - 1] = True
// #                 single = False
// #                 break
// #         if single:
// #             girl = i
// #     if girl == -1:
// #         print('OPTIMAL')
// #     else:
// #         print('IMPROVE')
// #         print(girl + 1, taken.index(False) + 1)
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     odd, even = [], []
// #     for i in range(2 * n):
// #         if a[i] % 2:
// #             odd.append(i + 1)
// #         else:
// #             even.append(i + 1)
// #     for i in range(n - 1):
// #         if len(odd) >= len(even):
// #             print(odd.pop(), odd.pop())
// #         else:
// #             print(even.pop(), even.pop())
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     a.sort()
// #     ans, i, j = 0, 0, 1
// #     while j < n:
// #         if a[i] < a[j]:
// #             ans += 1
// #             i += 1
// #             j += 1
// #         else:
// #             while j < n and a[i] == a[j]:
// #                 i += 1
// #                 j += 1
// #     print(ans + 1)
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     got = False
// #
// #     b = 1
// #     while not got and b < 2 * n - 1:
// #         if b % 2:
// #             i, j = (b - 1) // 2, (b + 1) // 2
// #         else:
// #             i, j = b // 2 - 1, b // 2 + 1
// #         left, right = set(a[:i]), set(a[j:])
// #         if left & right:
// #             got = True
// #         b += 1
// #     print('YES' if got else 'NO')
// 
// 
// # n, m, k = list(map(int, input().split()))
// # A = list(map(int, input().split()))
// # B = list(map(int, input().split()))
// # ans = 0
// # a, b = [0], [0]
// # for el in A:
// #     a.append(a[-1] + el)
// # for el in B:
// #     b.append(b[-1] + el)
// # d = [(i, k//i) for i in range(1, int(k**0.5)+1) if k % i == 0]
// # d += [(j, i) for i, j in d if i != j]
// # for i in range(n):
// #     for j in range(m):
// #         for q, p in d:
// #             if i + q <= n and j + p <= m:
// #                 if a[i + q] - a[i] == q and b[j + p] - b[j] == p:
// #                     ans += 1
// # print(ans)
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     s = input()
// #     dic, se = {s: 1}, {s}
// #     for k in range(2, n):
// #         p = s[k - 1:] + (s[:k - 1], s[:k - 1][::-1])[(n % 2) == (k % 2)]
// #         # print(k, p)
// #         if p not in dic:
// #             # print(dic, p)
// #             dic[p] = k
// #             se.add(p)
// #     if s[::-1] not in dic:
// #         dic[s[::-1]] = n
// #         se.add(s[::-1])
// #     # print(dic)
// #     ans = min(se)
// #     print(ans)
// #     print(dic[ans])
// 
// 
// # for t in range(int(input())):
// #     a, b, p = list(map(int, input().split()))
// #     s = input()
// #     road = [a if s[0] == 'A' else b]
// #     st = [0]
// #     for i in range(1, len(s) - 1):
// #         if s[i] != s[i - 1]:
// #             road.append(road[-1] + (a, b)[s[i] == 'B'])
// #             st.append(i)
// #     # print(road)
// #     pay = road[-1]
// #     j = 0
// #     while pay > p and j < len(st):
// #         pay = road[-1] - road[j]
// #         j += 1
// #     # print(j)
// #     print(st[j] + 1 if j < len(st) else len(s))
// 
// 
// # for t in range(int(input())):
// #     n, x, y = list(map(int, input().split()))
// #     print(max(1, min(x + y - n + 1, n)), min(n, x + y - 1))
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     print(' '.join(map(str, sorted(a, reverse=True))))
// 
// 
// # s = input()
// # open, close = [], []
// # i = 0
// # for i in range(len(s)):
// #     if s[i] == '(':
// #         open.append(i)
// #     else:
// #         close.append(i)
// # i, j = 0, len(close) - 1
// # ans = []
// # while i < len(open) and j >= 0 and open[i] < close[j]:
// #     ans += [open[i] + 1, close[j] + 1]
// #     i += 1
// #     j -= 1
// # ans.sort()
// # print('0' if not ans else '1\n{}\n{}'.format(len(ans), ' '.join([str(idx) for idx in ans])))
// 
// 
// import collections
// # n, m = list(map(int, input().split()))
// # a = list(input() for i in range(n))
// # dic = {}
// # for w in a:
// #     dic[w] = dic.get(w, 0) + 1
// # l, r = '', ''
// # for i in range(n):
// #     for j in range(i + 1, n):
// #         # print(i, j, a)
// #         if a[i] == a[j][::-1] and dic[a[i]] and dic[a[j]]:
// #             l += a[i]
// #             r = a[j] + r
// #             dic[a[i]] -= 1
// #             dic[a[j]] -= 1
// # c = ''
// # for k, v in dic.items():
// #     if v and k == k[::-1]:
// #         if c and c[-m] == k or not c:
// #             c += k
// # print(f'{len(l) + len(c) + len(r)}\n{l + c + r}')
// 
// 
// # for t in range(int(input())):
// #     n, g, b = list(map(int, input().split()))
// #     d = n // 2 + n % 2
// #     full, inc = divmod(d, g)
// #     ans = (g + b) * (full - 1, full)[inc > 0] + (g, inc)[inc > 0]
// #     print(ans if ans >= n else n)
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     a.sort()
// #     print(a[n] - a[n - 1])
// 
// 
// # for t in range(int(input())):
// #     n, x = list(map(int, input().split()))
// #     s = input()
// #     cntz = s.count('0')
// #     total = 2 * cntz - n
// #     bal = 0
// #     ans = 0
// #     for i in range(n):
// #         if not total:
// #             if bal == x:
// #                 ans = -1
// #         elif not abs(x - bal) % abs(total):
// #             if (x - bal) // total >= 0:
// #                 ans += 1
// #         bal += 1 if s[i] == '0' else -1
// #     print(ans)
// 
// 
// # n = int(input())
// # ans = 0
// # for i in range(1, n + 1):
// #     ans += 1 / i
// # print(ans)
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     p, s = 0, n - 1
// #     for i in range(n):
// #         if a[i] < i:
// #             break
// #         p = i
// #     for i in range(n - 1, -1, -1):
// #         if a[i] < n - i - 1:
// #             break
// #         s = i
// #     print('Yes' if s <= p else 'No')
// 
// 
// # n, k = list(map(int, input().split()))
// # a = [input() for i in range(n)]
// # c = set(a)
// # b = set()
// # for i in range(n):
// #     for j in range(i + 1, n):
// #         third = ''
// #         for c1, c2 in zip(a[i], a[j]):
// #             if c1 == c2:
// #                 third += c1
// #             else:
// #                 if c1 != 'S' and c2 != 'S':
// #                     third += 'S'
// #                 elif c1 != 'E' and c2 != 'E':
// #                     third += 'E'
// #                 else:
// #                     third += 'T'
// #         if third in c:
// #             b.add(frozenset([a[i], a[j], third]))
// # print(len(b))
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     total, curr = sum(a), 0
// #     ans, i, start = 'YES', 0, 0
// #     while ans == 'YES' and i < n:
// #         if curr > 0:
// #             curr += a[i]
// #         else:
// #             curr = a[i]
// #             start = i
// #         # print(curr, i, start, total)
// #         if i - start + 1 < n and curr >= total:
// #             ans = 'NO'
// #         i += 1
// #     print(ans)
// 
// 
// # for t in range(int(input())):
// #     n, p, k = list(map(int, input().split()))
// #     a = list(map(int, input().split()))
// #     a.sort(reverse=True)
// #     odd, even = 0, 0
// #     i, j = len(a) - 1, len(a) - 2
// #     curr = 0
// #     while curr < p and i >= 0:
// #         curr += a[i]
// #         if curr <= p:
// #             odd += 1
// #         i -= 2
// #     curr = 0
// #     while curr < p and j >= 0:
// #         curr += a[j]
// #         if curr <= p:
// #             even += 1
// #         j -= 2
// #     print(max(odd * 2 - 1, even * 2))
// 
// 
// # for t in range(int(input())):
// #     s, c = input().split()
// #     s = list(ch for ch in s)
// #     sor = sorted(s)
// #     for i in range(len(s)):
// #         if s[i] != sor[i]:
// #             j = max(j for j, v in enumerate(s[i:], i) if v == sor[i])
// #             s = s[:i] + [s[j]] + s[i + 1:j] + [s[i]] + s[j + 1:]
// #             break
// #     s = ''.join(s)
// #     print(s if s < c else '---')
// 
// 
// # for t in range(int(input())):
// #     n, s = list(map(int, input().split()))
// #     a = list(map(int, input().split()))
// #     if sum(a) <= s:
// #         print(0)
// #     else:
// #         curr, i, j = 0, 0, 0
// #         for i in range(n):
// #             if a[i] > a[j]:
// #                 j = i
// #             s -= a[i]
// #             if s < 0:
// #                 break
// #         print(j + 1)
// 
// 
// # for t in range(int(input())):
// #     a, b = list(map(int, input().split()))
// #     a, b = (b, a) if b > a else (a, b)
// #     if not ((1 + 8 * (a - b))**0.5 - 1) % 2 and ((1 + 8 * (a - b))**0.5 - 1) // 2 >= 0:
// #         ans = ((1 + 8 * (a - b))**0.5 - 1) // 2
// #         print(int(ans))
// #     else:
// #         n1 = int(((1 + 8 * (a - b))**0.5 - 1) // 2) + 1
// #         while (n1 * (n1 + 1) // 2) % 2 != (a - b) % 2:
// #             n1 += 1
// #         print(n1)
// 
// 
// # for t in range(int(input())):
// #     n = int(input())
// #     a = list(map(int, input().split()))
// #     a.sort()
// #     ans = 0
// #     l = 0
// #     dic = {}
// #     for i in range(n - 1, -1, -1):
// #         if not a[i] % 2:
// #             l, r = 0, 30
// #             while l < r:
// #                 m = (l + r) // 2
// #                 # print(l, r, m, a[i] % 2**m)
// #                 if a[i] % 2**m:
// #                     r = m
// #                 else:
// #                     l = m + 1
// #             dic[a[i] // 2**(l - 1)] = max(dic.get(a[i] // 2**(l - 1), 0), l - 1)
// #     print(sum(list(dic.values())))
// 
// 
// n = int(input())
// s = input()
// b = s.count('B')
// w = n - b
// if b % 2 and w % 2:
//     print(-1)
// elif not b or not w:
//     print(0)
// else:
//     ans = []
//     if not b % 2:
//         for i in range(n - 1):
//             if s[i] != 'W':
//                 ans += [str(i + 1)]
//                 s = s[:i] + 'W' + 'BW'[s[i + 1] == 'B'] + s[i + 2:]
//     elif not w % 2:
//         for i in range(n - 1):
//             if s[i] != 'B':
//                 ans += [str(i + 1)]
//                 s = s[:i] + 'B' + 'WB'[s[i + 1] == 'W'] + s[i + 2:]
//     print(len(ans))
//     print(' '.join(ans))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, is_white_list: seq<bool>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
