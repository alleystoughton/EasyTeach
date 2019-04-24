Eager/Lazy Random Sampling
====================================================================

This subdirectory shows how to switch back and forth between eager and
lazy random sampling. This is done using an abstract theory for
handling redundant hashing.

The abstract theory [`RedundantHashing.eca`](RedundantHashing.eca) is
proved using EasyCrypt's eager tactics, as well as its transitivity
tactic. (It uses the auxiliary theories [`FSetAux.ec`](FSetAux.ec) and
[`ListAux.ec`](ListAux.ec)).

And [`EagerEx.ec`](EagerEx.ec) is proved using 
[`RedundantHashing.eca`](RedundantHashing.eca).
