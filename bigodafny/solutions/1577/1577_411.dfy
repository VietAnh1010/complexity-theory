// 1155_A. Reverse a Substring  (problem 1577, solution 1577_411)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def main():
//     n = int(input())
//     s = input()
// 
//     try:
//         index = next(i for i in range(n - 1) if s[i] > s[i + 1])
//         print('YES\n%d %d' % (index + 1, index + 2))
//     except StopIteration:
//         print('NO')
// 
// 
// if __name__ == '__main__':
//     main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, s: string) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
