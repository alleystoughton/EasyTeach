Symmetric Encryption from Pseudorandom Functions
====================================================================

This subdirectory contains the proof of IND-CPA (indistinguishability
under chosen plaintext attack) security for symmetric encryption built
out of a pseudorandom function.

The theory [`SymEnc.ec`](SymEnc.ec) gives the
general definition of a symmetric encryption scheme, and says what it
means for such a scheme to be IND-CPA secure.

The theory [`PseudoRandFun.ec`](PseudoRandFun.ec)
defines pseudorandom functions (PRFs) and says what it means
for a PRF to be secure.

And [`SymEnc-PRF.ec`](SymEnc-PRF.ec) defines a concrete symmetric
encryption scheme out of a PRF, and then proves the IND-CPA security
of this scheme, reducing it to the security of the PRF. This proof
illustates the use of the sequence of games approach, upto bad
reasoning, and EasyCrypt's failure event lemma for upper-bounding the
probability of a failure event holding.
