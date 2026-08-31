// 883_F. Lost in Transliteration  (problem 2704, solution 2704_62)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #### Answer to <https://codeforces.com/problemset/problem/251/A>
// # import math
// 
// # count, bounds = [int(x) for x in input().split(" ")]
// # total = 0
// 
// # left_index = 0
// # right_index = 2
// # current = 0
// 
// # lst = [int(x) for x in input().split(" ")]
// # if lst[0] < 0:
// #     delta = 1 - lst[0]
// #     lst = [x + delta for x in lst]
// 
// # while right_index < len(lst):
// #     if lst[right_index] - lst[left_index] <= bounds:
// #         right_index += 1
// #         continue
// #     elements = right_index - left_index - 1
// #     total += elements * (elements - 1) / 2
// #     left_index += 1
// 
// # while left_index < len(lst) - 2:
// #     if lst[count-1] - lst[left_index] <= bounds:
// #         elements = count - left_index - 2
// #         total += elements * (elements + 1) / 2
// #         left_index += 1
// # print(int(total))
// 
// # ### Answer to <https://codeforces.com/contest/38/problem/C>
// # count, bounds = [int(x) for x in input().split(" ")]
// # lst = [int(x) for x in input().split(" ")]
// # lst.sort()
// 
// 
// # right_index = count - 1
// # left_index = 0
// # highest = 0
// # current_num = -1
// 
// # # Find left most index where number is greater than or equal to bounds
// # for index, i in enumerate(lst):
// #     if i < bounds:
// #         left_index += 1
// #         continue
// #     break
// 
// # while right_index >= left_index:
// #     # Same number as before, no need to check
// #     if lst[left_index] == current_num:
// #         left_index += 1
// #         continue
// 
// #     # Different Number
// #     current_num = lst[left_index]
// 
// #     for j in range(current_num, bounds-1, -1):
// #         current = 0
// #         for i in range(left_index, right_index + 1):
// #             # Add maximum possible
// #             current += (lst[i] // j) * j
// #         # print("L:", left_index, "| R:", right_index, "current:", current)
// #         if current > highest:
// #             highest = current
// #     left_index += 1
// 
// # print(highest)
// 
// #### <https://codeforces.com/problemset/problem/617/B>
// # def solve():
// #     numbers = int(input())
// #     lst = [int(x) for x in input().split(" ")]
// #     add = sum
// #     if add(lst) <= 1:
// #         print(add(lst))
// #         return
// #     elif add(lst) == len(lst):
// #         print(1)
// #         return
// 
// #     left_index = lst.index(1) # First occurence of a nut
// #     right_index = left_index
// 
// #     for i in range(left_index, len(lst)):
// #         if lst[i] == 1:
// #             right_index = i
// #             break
//     
// #     total = 1
// #     while right_index < len(lst):
// #         if lst[right_index] == 1:
// #             delta = right_index - left_index
// #             total *= max(1, delta)
// #             left_index = right_index
// #         right_index += 1
// #     print(total)
// # solve()
// 
// #### <https://codeforces.com/contest/617/problem/C> UNSOLVED
// # def solve():
// #     total = 0
// #     n, r_x, r_y, s_x, s_y = list(map(int, input().split(" ")))
// #     flowers = []
// #     for i in range(n):
// #         flowers.append(list(map(int, input().split(" "))))
// 
// #     r_list = []
// #     s_list = []
// #     flowers_list = []
// #     for index, i in enumerate(flowers):
// #         distance_r = (r_x - i[0])**2 + (r_y - i[1])**2
// #         distance_s = (s_x - i[0])**2 + (s_y - i[1])**2
// #         # r_list.append((index, distance_r))
// #         # s_list.append((index, distance_s))
// 
// #         flowers_list.append((index, distance_r, "R"))
// #         flowers_list.append((index, distance_s, "S"))
// 
// #     flowers_list.sort(key=lambda x:x[1])
// 
// 
// #     # r_list.sort(key=lambda x:x[1])
// #     # s_list.sort(key=lambda x:x[1])
// 
// #     # lowest = int(s_list[-1][1]) + 1
// #     # for index, j in enumerate(s_list):
// #     #     current = 0
// 
// #     #     # Show all the flowers that are being given to r
// #     #     r_tmp = []
// #     #     for i in range(index, len(s_list)):
// #     #         r_tmp.append(s_list[i][0])
// 
// 
// #     # print(r_list)
// #     # print(s_list)
// #     print(flowers_list)
// #     flower_freq = {}
// #     for i in range(n):
// #         flower_freq[i] = 0
// 
// 
// #     val1 = flowers_list[-1][0]
// #     val2 = 0
// #     if flowers_list[-1][-1] == 'S':
// #         highest = 'R'
// #     else:
// #         highest = 'S'
// 
// 
// #     for i in range(n):
// #         flowers_freq[flowers_list[i][0]] += 1
// #         if flowers_list[i][2] != highest:
// #             val2 = flowers_list[i][0]
// #     # total = r1 + r2
// #     # print(total)
// # solve()
// 
// #### Solution <https://codeforces.com/problemset/problem/615/A>
// # def solve():
// #     groups, lights = list(map(int, input().split(" ")))
// #     lst = []
// 
// #     for i in range(groups):
// #         group = list(map(int, input().split(" ")))
// #         num = group.pop(0)
// #         lst = lst + group
// #     lst = list(set(lst))
// #     if len(lst) == lights:
// #         print("YES")
// #     else:
// #         print("NO")
//  
// 
// # solve()
// 
// #### Solution <https://codeforces.com/problemset/problem/614/A>
// # def solve():
// #     l, r, k = list(map(int, input().split(" ")))
// #     lst = []
// #     count = 0
// #     while k ** count <= r:
// #         if k ** count >= l:
// #             lst.append(k ** count)
// #         count += 1
// #     if len(lst) == 0:
// #         print(-1)
// #     else:
// #         print(" ".join([str(x) for x in lst]))
// 
// # solve()
// 
// def solve():
//     n = int(input())
//     words = {}
//     for i in range(n):
//     	word = input()
//     	while "u" in word:
//     		word = word.replace("u", "oo")
//     	while "kkh" in word:
//     		word = word.replace("kkh", "kh")
//     	if "kh" in word:
//     		word = word.replace("kh", "h")
//     	if word not in words:
//     		words[word] = 1
//     	else:
//     		words[word] += 1
//     print(len(words))
// solve()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, names: seq<string>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
