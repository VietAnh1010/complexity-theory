// Without enable=functions, a call to the row's own function stops annotate.
function CountZeros(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0 else (if s[0] == 0 then 1 else 0) + CountZeros(s[1..])
}

method Solve(a: seq<int>) returns (output: int)
{
  output := CountZeros(a);
}
