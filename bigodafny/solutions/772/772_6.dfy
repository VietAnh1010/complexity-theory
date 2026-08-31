// 339_D. Xenia and Bit Operations  (problem 772, solution 772_6)
// time complexity: O(n)
// python exact-diff baseline: exact
//
// Reproduce the Python program's entire stdout in `output`.
//
// --- Python ---------------------------------------------------------
// #Xenia and Bit Operations
// #from operator import or_, xor
// import sys
// 
// def ispow2(n): #doesn't work for n = 0.
//     neg = n & (n-1)
//     if neg == 0:
//         return True
//     else:
//         return False
// 
// def build_seg_tree(n, a): #n is length of a. Tree will have high-level nodes from 1 to n-1, and array will start at n to 2n-1, for a total length of 2n.
//     #Position 0 will be 0 and unused.
//     tree = [0] * (n) #upper nodes of tree.
//     tree.extend(a) #leaves of tree.
//     #Build upper nodes. 
//     ###Unique based on specific problem, but always tree[i] based on tree[2*i] and tree[(2*i)+1]
//     or_level = True
//     for i in range(n-1, 0, -1):
//         if or_level:
//             tree[i] = tree[2*i] | tree[(2*i)+1]
//         else:
//             tree[i] = tree[2*i] ^ tree[(2*i)+1]
//         if ispow2(i):
//             or_level = not or_level
//     #print('initial tree=', tree)
//     return tree
// 
// def modify_seg_tree(tree, pos, val):
//     n = len(tree) // 2
//     pos += n #Converts to n-based array in tree.
//     tree[pos] = val #initial change based on query from CF.
//     or_level = True
//     while pos > 1:
//         pos = pos // 2
//         if or_level:
//             tree[pos] = tree[2*pos] | tree[(2*pos)+1]
//         else:
//             tree[pos] = tree[2*pos] ^ tree[(2*pos)+1]
//         
//         or_level = not or_level
//         
//     #print(tree)
// 
//     return
// 
// def query_seg_tree(tree, pos):
//     #This problem pos = 1
//     return tree[pos]
// 
// def answer(n, m, a, p, b):
//     #answer gets called once.
//     #Build segment tree
//     tree = build_seg_tree(2**n, a) #This specific problem gave length as power of two.
//     for i in range(m): # # of queries
//         modify_seg_tree(tree, p[i]-1, b[i]) #i-1 because CF uses 1-based arrays and we want 0-based arrays.
//         print(query_seg_tree(tree, 1)) # usually lpos & rpos, but here only 1 because the modification affects the top.
//         #print(tree[1])
//     return 
// 
// def main():
//     n, m = [int(i) for i in input().split()]
//     a = [int(i) for i in input().split()]
//     p = [0] * m
//     b = [0] * m
//     for j in range(m):
//         #p[j], b[j] = [int(i) for i in input().split()]
//         p[j], b[j] = [int(i) for i in sys.stdin.readline().split()]
//     answer(n, m, a, p, b)
// 
//     return
// 
// main()
// --------------------------------------------------------------------

include "../../prelude.dfy"
import opened Prelude

method Solve(n: int, m: int, weights: seq<int>, edges: seq<seq<int>>) returns (output: string)
{
  output := ""; // TODO: translate the Python above
}
