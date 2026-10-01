// LABEL AUDIT -- queued for manual review, not a decision.
//
//   stated label   : O(1)
//   audited class  : other
//   cause          : label
//   confidence     : medium
//   auditor        : labelaudit-r3d-04
//
//   The PYTHON is not the labelled class either. BigOBench's label looks
//   wrong; the translation is faithful to it.
//
//   evidence:
//     Z(n) calls ToBinary(n), which recurses on n/2 and so has depth
//     log2(n), then CountZeros and FindZero scan the whole binary string,
//     so the cost is O(log a + log b) in the input VALUES; the Python's
//     bin(n)[2:], n.count('0') and n.find('0') are linear in the same bit
//     length.
//
//   how this label could be wrong, and what to check:
//     The label treats the work as constant, presumably because a,b <=
//     10**18. A statement cap does not make a value term constant under
//     the current rules; open ToBinary (recursion on n/2) and CountZeros,
//     which are bounded by the bit length of the argument. If the dataset
//     deems 64-bit binary conversion free, the label would stand.
//
//   structural facts (deterministic, from label_audit.py):
//     {"body_lines": 39, "data_dependent_loops": 0, "decreases_star":
//     false, "linear_prelude_calls": ["IntToString"], "loop_depth": 0,
//     "loops": 0, "recursive_helpers": 4, "seq_append_read_in_same_loop":
//     false, "seq_args": 0, "seq_update_in_loop": false,
//     "set_build_in_loop": false, "sorts": [], "uses_map": false,
//     "uses_multiset": false, "uses_set": false}
// --------------------------------------------------------------------

// 611_B. New Year and Old Property  (problem 1364, solution 1364_163)
// time complexity: O(1)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// def z(n):
//     n = bin(n)[2:]
//     k = len(n)
//     s = (k-1) * (k-2) // 2 + (n.count("0") == 1)
//     r = n.find("0")
//     s += k if r == -1 else r
//
//     return s - 1;
//
// a, b = map(int, input().split());
// print (z(b) - z(a - 1))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

function ToBinary(n: int): string
  requires n >= 0
  decreases n
{
  if n == 0 then "0"
  else if n == 1 then "1"
  else ToBinary(n / 2) + (if n % 2 == 0 then "0" else "1")
}

function CountZeros(s: string): int
  decreases |s|
{
  if |s| == 0 then 0
  else (if s[0] == '0' then 1 else 0) + CountZeros(s[1..])
}

function FindZero(s: string): int
  decreases |s|
{
  if |s| == 0 then -1
  else if s[0] == '0' then 0
  else (var r := FindZero(s[1..]); if r == -1 then -1 else r + 1)
}

function Z(n: int): int
  requires n >= 0
{
  var bs := ToBinary(n);
  var k := |bs|;
  var s := (k - 1) * (k - 2) / 2 + (if CountZeros(bs) == 1 then 1 else 0);
  var r := FindZero(bs);
  var s2 := s + (if r == -1 then k else r);
  s2 - 1
}

method Solve(a: int, b: int) returns (output: string)
  requires a >= 1
  requires b >= 0
{
  output := IntToString(Z(b) - Z(a - 1));
}
