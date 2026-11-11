// --- Python ---------------------------------------------------------
// def settle(c):
//     n = len(c)
//     stack = [i for i in range(n) if c[i] >= 2]
//     moves = 0
//     while stack:
//         i = stack.pop()
//         c[i] -= 2
//         moves += 1
//         if i > 0:
//             c[i - 1] += 1
//             if c[i - 1] == 2:
//                 stack.append(i - 1)
//         if i + 1 < n:
//             c[i + 1] += 1
//             if c[i + 1] == 2:
//                 stack.append(i + 1)
//         if c[i] >= 2:
//             stack.append(i)
//     return moves
//
// n = int(input())
// c = list(map(int, input().split()))
// moves = settle(c)
// print(moves, sum(c))
// --------------------------------------------------------------------

include "../../../prelude.dfy"
import opened Prelude

method Settle(c: array<int>) returns (moves: int)
  modifies c
  requires forall i :: 0 <= i < c.Length ==> 0 <= c[i] <= 3
  decreases *
{
  var n := c.Length;
  var stack := new int[n + 1];
  var top := 0;
  var k := 0;
  while k < n
    decreases *
  {
    if c[k] >= 2 {
      stack[top] := k;
      top := top + 1;
    }
    k := k + 1;
  }
  moves := 0;
  while top > 0
    decreases *
  {
    top := top - 1;
    var i := stack[top];
    c[i] := c[i] - 2;
    moves := moves + 1;
    if i > 0 {
      c[i - 1] := c[i - 1] + 1;
      if c[i - 1] == 2 {
        stack[top] := i - 1;
        top := top + 1;
      }
    }
    if i + 1 < n {
      c[i + 1] := c[i + 1] + 1;
      if c[i + 1] == 2 {
        stack[top] := i + 1;
        top := top + 1;
      }
    }
    if c[i] >= 2 {
      stack[top] := i;
      top := top + 1;
    }
  }
}

method Solve(n: int, a_list: seq<int>) returns (output: string)
  requires n >= 1 && |a_list| == n
  requires forall i :: 0 <= i < n ==> 0 <= a_list[i] <= 3
  decreases *
{
  var c := new int[n];
  var k := 0;
  while k < n
    decreases *
  {
    c[k] := a_list[k];
    k := k + 1;
  }
  var moves := Settle(c);
  var left := 0;
  k := 0;
  while k < n
    decreases *
  {
    left := left + c[k];
    k := k + 1;
  }
  output := IntToString(moves) + " " + IntToString(left);
}
