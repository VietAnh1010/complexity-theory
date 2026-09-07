// p03776 AtCoder Beginner Contest 057 - Maximum Average Sets  (problem 3079, solution 3079_85)
// time complexity: O(nlogn)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// N, A, B = map(int, input().split())
// val = [int(i) for i in input().split()]
// 
// def combi(n, m):
//     from math import factorial
//     return factorial(n) // (factorial(m) * factorial(n-m))
// 
// val.sort(reverse=True)
// ave = sum(val[:A])/A
// 
// l = val.index(val[A-1])
// x = val.count(val[A-1])
// ct = 0
// 
// if val[0] == val[A-1]:
//     for i in range(A, x+1):
//         if i > B:
//             break
//         else:
//             ct += combi(x, i)
// else:
//     ct = combi(x, A-l)
// print(ave)
// print(ct)
// --------------------------------------------------------------------

// ===================================================================
// NOT TRANSLATED — and not intended to be.
//
// Blocker: print(ave) where ave is a Python float mean
//
// Reproducing this byte-for-byte needs two things Dafny cannot give:
//   1. bit-exact IEEE-754 double arithmetic. Dafny's `real` is an exact
//      rational, so it does not round where a float rounds, and the two
//      diverge before any printing happens.
//   2. CPython's shortest-round-trip float repr (Grisu/Dragon4). `print(x)`
//      on a float emits the shortest decimal string that parses back to the
//      same double -- not a fixed number of digits.
//
// Detail: ave is a float mean printed bare.
//
// This is decidable and tractable when the Python uses a FORMAT SPEC:
// solutions/2496/2496_30.dfy computes in exact rationals and hand-writes
// FormatG9 to replicate '{:.9}'.format(x), and agrees on all 42 comparable
// tests. It is the bare `print(float)` that has no finite specification.
//
// Both gates are therefore inapplicable, not merely failing:
// validate.py and difftest.py both compare stdout as text.
// ===================================================================

