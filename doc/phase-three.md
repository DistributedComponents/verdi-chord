Let *L* be the maximum length of successor lists.

Let the error of a successor list be the length of its longest globally correct
prefix. When a node *h* stabilizes with its correct first successor *s* and the
error at *s* is *e*, the error at *h* becomes max(*e* - 1, 0).

Since we're done with phase two and all first successors are correct, each node
has error at most *L* - 1. Each node can stabilize to obtain error at most *L*
- 2.

Suppose that all nodes have error at most *L* - *k*, where *k* > 1. Each node
can stabilize to obtain error at most max(*L* - *k* - 1, 0).

By induction on maximum error, this shows that eventually all nodes have error
0, i.e., correct successor lists of length *L*.
