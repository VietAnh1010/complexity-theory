// 978_B. File Name  (problem 2226, solution 2226_607)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// from math import ceil, log, floor, sqrt
// import math	
// 	
// 	
// k = 1	
// def mod_expo(n, p, m):
// 	"""find (n^p)%m"""
// 	result = 1
// 	while p != 0:
// 		if p%2 == 1:
// 			result = (result * n)%m
// 		p //= 2
// 		n = (n * n)%m
// 	return result
// 	
// def is_prime(n):
// 	m = 2
// 	while m*m <= n:
// 		if n%m == 0:
// 			return False
// 		m += 1
// 	return True
// 	
// def find_sum(n, a):
// 	a.insert(0, 0)
// 	for i in range(1, n+1):
// 		prev = a[i] & a[i-1]
// 		cur = a[i] | a[i-1]
// 		a[i-1] = prev
// 		a[i] = cur
// 	return sum(m*m for m in a)
// 
// def prin_abc(x, y, z):
// 	l = [x, y, z]
// 	l.sort()
// 	if l[1] < l[2]:
// 		print("NO")
// 		return 
// 	a = b = l[0]
// 	c = l[2]
// 	print("YES")
// 	print(a, b, c)
// 	
// def get_scores(n, vals):
// 	l = 0
// 	r = n-1
// 	turn = 0
// 	sereja = 0
// 	dima = 0
// 	while l <= r:
// 		if vals[l] > vals[r]:
// 			cur = vals[l]
// 			l += 1
// 		else:
// 			cur = vals[r]
// 			r -= 1
// 		if turn == 0:
// 			sereja += cur
// 		else:
// 			dima += cur
// 		turn = not turn
// 	print(sereja, dima)
// 		
// def count_lamps(n, m):
// 	return (n*m + 1)//2
// 	
// def count_moves(n, name):
// 	mvs = 0
// 	cnt = 0
// 	for i in range(n):
// 		if name[i] == 'x':
// 			cnt += 1
// 		else:
// 			mvs += max(0, cnt-2)
// 			cnt = 0
// 	mvs += max(0, cnt-2)
// 	return mvs
// 		
// t = 1
// #t = int(input())
// while t:
// 	t = t - 1
// 	points = []
// 	n = int(input()) 
// 	name = input()
// 	#a, b, k = map(int, input().split()) 
// 	#print(discover())
// 	# = map(int, input().split())
// 	#a = list(map(int, input().strip().split()))[:n]
// 	#w = list(map(int, input().strip().split()))[:k]
// 	#for i in range(3):
// 	#	x, y = map(int, input().split()) 
// 	#	points.append((x, y))
// 	#s = input()
// 	#if solvable(n, m):
// 	#	print("YES")
// 	#else:
// 	#	print("NO")
// 	
// 	print(count_moves(n, name))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, binary_string: string) returns (output: string)
{
  var mvs := 0;
  var cnt := 0;
  var i := 0;
  while i < n
    decreases n - i
  {
    if binary_string[i] == 'x' {
      cnt := cnt + 1;
    } else {
      var extra := cnt - 2;
      mvs := mvs + (if extra > 0 then extra else 0);
      cnt := 0;
    }
    i := i + 1;
  }
  var extra2 := cnt - 2;
  mvs := mvs + (if extra2 > 0 then extra2 else 0);
  output := IntToString(mvs);
}
