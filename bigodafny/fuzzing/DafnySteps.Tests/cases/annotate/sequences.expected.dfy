
method Solve(s: seq<int>, t: seq<int>, x: int)
    returns (output: seq<int>, ghost steps: nat)
{
  steps := 0;
  steps := steps + |t|;
  var u := s + t;
  steps := steps + 4;
  var v := [x, x + 1, 0];
  steps := steps + 1;
  var w := u[0 := x];
  steps := steps + (1 + |v|);
  output := w[1..] + v;
}
