// 1388_B. Captain Flint and a Long Voyage  (problem 721, solution 721_309)
// time complexity: O(nlogn)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// 
// import sys
// sys.setrecursionlimit(10000)
// # default is 1000 in python
// 
// 
// t = int(input())
// # t = 1
// 
// for _ in range(t):
// 	n = int(input())
// 
// 	remain = n % 4
// 	times = n // 4
// 	y = "8" * times
// 	z = ""
// 	if remain != 0:
// 		z = "8"
// 
// 	# z+y
// 	digleft = n - times - 1
// 	if remain == 0:
// 		digleft += 1
// 	x = "9"*digleft
// 	x = x + z + y
// 	print(x)
// 
// # try:
// 	# raise Exception
// # except:
// 	# print("-1")
// 
// 
// # from collections import OrderedDict 
// # mydict = OrderedDict() 
// 
// 
// # thenos.sort(key=lambda x: x[2], reverse=True)
// 
// # int(math.log(max(numbers)+1,2))
// 
// # 2**3 (power)
// 
// # a,t = (list(x) for x in zip(*sorted(zip(a, t))))
// 
// # to copy lists use .copy()
// 
// # pow(p, si, 1000000007) for modular exponentiation
// 
// # my_dict.pop('key', None)
// # This will return my_dict[key] if key exists in the dictionary, and None otherwise.
// 
// 
// 
// # bin(int('010101', 2))
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, numbers: seq<int>) returns (output: string)
{
  var lines: seq<string> := [];
  var i := 0;
  while i < |numbers|
    decreases |numbers| - i
  {
    var m := numbers[i];
    var remain := FloorMod(m, 4);
    var times := FloorDiv(m, 4);
    var timesNat := if times >= 0 then times as nat else 0;
    var yPart := Repeat("8", timesNat);
    var zPart := if remain != 0 then "8" else "";
    var digleft := m - times - 1;
    if remain == 0 {
      digleft := digleft + 1;
    }
    var digleftNat := if digleft >= 0 then digleft as nat else 0;
    var xPart := Repeat("9", digleftNat);
    lines := lines + [xPart + zPart + yPart];
    i := i + 1;
  }
  output := Join(lines, "\n");
}
