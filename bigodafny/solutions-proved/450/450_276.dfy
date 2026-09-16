// 1421_C. Palindromifier  (problem 450, solution 450_276)
// time complexity: O(n)
// python exact-diff baseline: none
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def isPalin(st):
//
//     i,j=0,len(st)-1
//     while(i<=j):
//         if(st[i]==st[j]):
//             i+=1
//             j-=1
//         else:
//             return False
//     return True
//
//
// def proC(st):
//     if(isPalin(st)):
//         print(0)
//         return
//     print(3)
//     print('R',len(st)-1)
//     print('L',len(st))
//     print('L',2)
// n=input()
// proC(n)
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(s: string) returns (output: string, ghost steps: nat)
  ensures steps <= 4 * |s| + 8
{
  IsPalinCostBound(s, 0, |s| - 1);
  if IsPalindrome(s) {
    output := "0\n";
    steps := IsPalinCost(s, 0, |s| - 1) + 1;
  } else {
    output := "3\n" + "R " + IntToString(|s| - 1) + "\n" + "L " + IntToString(|s|) + "\n" + "L 2\n";
    steps := IsPalinCost(s, 0, |s| - 1) + 4;
  }
}

function IsPalindrome(s: string): bool
{
  IsPalinFrom(s, 0, |s| - 1)
}

function IsPalinFrom(s: string, i: int, j: int): bool
  requires 0 <= i <= |s|
  requires -1 <= j < |s|
  decreases j - i
{
  if i >= j then true
  else if s[i] != s[j] then false
  else IsPalinFrom(s, i + 1, j - 1)
}

// ---- proof-only cost accounting --------------------------------------
// Label O(n). IsPalinFrom does O(1) work (two indexings, a comparison) per
// call, and each call shrinks j - i by 2, so the recursion depth is at
// most |s|.
ghost function IsPalinCost(s: string, i: int, j: int): nat
  requires 0 <= i <= |s|
  requires -1 <= j < |s|
  decreases j - i
{
  if i >= j then 1
  else if s[i] != s[j] then 1
  else 1 + IsPalinCost(s, i + 1, j - 1)
}

lemma IsPalinCostBound(s: string, i: int, j: int)
  requires 0 <= i <= |s|
  requires -1 <= j < |s|
  requires i <= j + 1
  ensures IsPalinCost(s, i, j) <= j - i + 2
  decreases j - i
{
  if i >= j {
  } else if s[i] != s[j] {
  } else {
    IsPalinCostBound(s, i + 1, j - 1);
  }
}
