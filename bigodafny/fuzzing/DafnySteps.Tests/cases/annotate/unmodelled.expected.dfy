
method Solve(n: nat) returns (output: seq<int>, ghost steps: nat)
{
  steps := 0;
  steps := steps + n;
  var s := seq(n, i => i * 2);
  steps := steps + 1;
  var t := set x | x in s && x > 0;
  output := s;
}
