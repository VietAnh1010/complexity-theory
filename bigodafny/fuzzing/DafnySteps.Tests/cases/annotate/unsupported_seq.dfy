// Without enable=seq, seq(n, f) stops annotate.
method Solve(n: nat) returns (output: seq<int>)
{
  output := seq(n, _ => 0);
}
