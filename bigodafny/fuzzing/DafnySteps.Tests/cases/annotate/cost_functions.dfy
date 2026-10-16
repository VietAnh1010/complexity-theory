// Each function F gets a ghost cost function F_steps with F's parameters,
// requires and decreases; a call F(x) is charged F_steps(x). A recursive call
// inside F costs F_steps too.
function CountZeros(s: seq<int>): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == 0 then 1 else 0) + CountZeros(s[1..])
}

predicate Contains(s: seq<int>, v: int, i: nat)
  requires i <= |s|
  decreases |s| - i
{
  i < |s| && (s[i] == v || Contains(s, v, i + 1))
}

method Solve(a: seq<int>, v: int) returns (output: int)
{
  output := CountZeros(a);
  if Contains(a, v, 0) {
    output := output + 1;
  }
}
