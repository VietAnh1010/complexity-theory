// 68_B. Energy exchange  (problem 967, solution 967_5)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// n, k = map(int, input().split())
// a = sorted(list(map(int, input().split())))
//  
// left = 0
// right = a[-1]
// for i in range(100):
//     mid = (left + right) / 2.0
//  
//     s1 = sum([x - mid for x in a if x >= mid]) * (100 - k) / 100.0
//     s2 = sum([mid - x for x in a if x < mid])
//     
//     if s1 >= s2:
//         left = mid
//     else:
//         right = mid
//  
// print(left)
// --------------------------------------------------------------------

// ===================================================================
// NOT TRANSLATED — and not intended to be.
//
// Blocker: print(left) where left is a Python float from binary search
//
// Reproducing this byte-for-byte needs two things Dafny cannot give:
//   1. bit-exact IEEE-754 double arithmetic. Dafny's `real` is an exact
//      rational, so it does not round where a float rounds, and the two
//      diverge before any printing happens.
//   2. CPython's shortest-round-trip float repr (Grisu/Dragon4). `print(x)`
//      on a float emits the shortest decimal string that parses back to the
//      same double -- not a fixed number of digits.
//
// Detail: left is a float bisection bound printed bare.
//
// This is decidable and tractable when the Python uses a FORMAT SPEC:
// solutions/2496/2496_30.dfy computes in exact rationals and hand-writes
// FormatG9 to replicate '{:.9}'.format(x), and agrees on all 42 comparable
// tests. It is the bare `print(float)` that has no finite specification.
//
// Both gates are therefore inapplicable, not merely failing:
// validate.py and difftest.py both compare stdout as text.
// ===================================================================

