Eager/Lazy Random Sampling
====================================================================

The subdirectory shows how to switch back and forth between eager and
lazy random sampling. This is done using an abstract theory for
handling redundant hashing.

The abstract theory [`RedundantHashing.eca`](RedundantHashing.ec) is
proved using EasyCrypt's eager tactics, as well as its transitivity
tactic.

And [`EagerEx.ec`](EagerEx.ec) is proved using 
[`RedundantHashing.eca`](RedundantHashing.ec).
