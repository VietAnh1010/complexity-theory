// A set comprehension is not in the cost model: annotate stops.
method Solve(n: nat, s: seq<int>) returns (output: seq<int>)
{
  var t := set x | x in s && x > 0;
  output := s;
}
