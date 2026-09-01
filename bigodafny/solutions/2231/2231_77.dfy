// 1105_B. Zuhair and Strings  (problem 2231, solution 2231_77)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// k = int(input().split()[1])
// result = {}
// prev = 0
// value = 0
// STR = input() + '$'
// 
// for letter in STR:
//     if letter != prev:
//         result[prev] = result.get(prev, 0) + value//k
//         prev = letter
//         value = 0
//     value+=1
// 
// print(max(result.values()))  
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(a: int, b: int, string_: string) returns (output: string)
{
  var k := b;
  var strSeq := string_ + "$";
  var entries: seq<(char,int)> := [];
  var prev := '\0';
  var value := 0;
  var i := 0;
  while i < |strSeq|
    decreases |strSeq| - i
  {
    var letter := strSeq[i];
    if letter != prev {
      var addition := FloorDiv(value, k);
      var found := false;
      var newEntries: seq<(char,int)> := [];
      var j := 0;
      while j < |entries|
        decreases |entries| - j
      {
        if entries[j].0 == prev {
          newEntries := newEntries + [(prev, entries[j].1 + addition)];
          found := true;
        } else {
          newEntries := newEntries + [entries[j]];
        }
        j := j + 1;
      }
      if !found { newEntries := newEntries + [(prev, addition)]; }
      entries := newEntries;
      prev := letter;
      value := 0;
    }
    value := value + 1;
    i := i + 1;
  }
  var vals: seq<int> := [];
  var j2 := 0;
  while j2 < |entries|
    decreases |entries| - j2
  {
    vals := vals + [entries[j2].1];
    j2 := j2 + 1;
  }
  output := IntToString(MaxSeq(vals));
}
