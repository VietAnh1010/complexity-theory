// A ghost function in a flow becomes compiled, with the functions it calls.
// Unused stays ghost.
ghost function Square(n: nat): nat { n * n }
ghost function Cost(n: nat): nat { Square(n) + 1 }
ghost function Unused(n: nat): nat { n }

method Solve(n: nat) returns (output: int, ghost steps: nat)
{
  steps := Cost(n);
  output := n;
}
