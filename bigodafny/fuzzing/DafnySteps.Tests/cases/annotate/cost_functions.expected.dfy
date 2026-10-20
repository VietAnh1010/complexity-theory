
function CountZeros(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then
    0
  else
    (if s[0] == 0 then 1 else 0) + CountZeros(s[1..])
}

ghost function CountZeros_steps(s: seq<int>): nat
  decreases |s|
{
  3 + if |s| == 0 then 0 else 5 + CountZeros_steps(s[1..])
}

predicate Contains(s: seq<int>, v: int, i: nat)
  requires i <= |s|
  decreases |s| - i
{
  i < |s| &&
  (s[i] == v || Contains(s, v, i + 1))
}

ghost function Contains_steps(s: seq<int>, v: int, i: nat): nat
  requires i <= |s|
  decreases |s| - i
{
  3 + if i < |s| then 3 + if s[i] == v then 0 else 1 + Contains_steps(s, v, i + 1) else 0
}

method Solve(a: seq<int>, v: int)
    returns (output: int, ghost steps: nat)
{
  steps := 0;
  steps := steps + CountZeros_steps(a);
  output := CountZeros(a);
  steps := steps + Contains_steps(a, v, 0);
  if Contains(a, v, 0) {
    steps := steps + 1;
    output := output + 1;
  }
}
